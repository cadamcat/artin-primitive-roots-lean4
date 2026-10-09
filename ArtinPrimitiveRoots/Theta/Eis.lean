import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.LocalWhit
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.Cosets
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.ComplexMajorant
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.ComplexIntegral
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.FiniteProduct
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.CubeClasses
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.LocalValuation
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_CONVERGE.FiniteMajorant
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GLOBAL-DATUM».LocalModel
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.GoodFactor
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.GaussBound
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.SphericalBound
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.QuotientCoordinates
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.ValuationGeometry
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.OrdinaryClasses
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.IdealEncoding
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.RationalEncoding
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.IdealMajorant
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.LocalProduct
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.PeriodLattice
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.FullJacquet
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.FourierDilation
import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.ComplexFourier

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-EIS -/

section Eis

open MeasureTheory

variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- **def:global-datum** (10:46–58; KP §II.1 pp. 107–109 made explicit). At every finite place a
torus representation `T v` with the evaluation functional `lam v` of its induced model, equivariant
under the Lagrangian subgroup `Alag v` with character `ω v`; tame normalization outside `S`; and the
global-datum condition: `Π_{v∈S} ω_v(δ) = 1` for rational `δ` in every `Alag v`. C6 of
`sol-gate-theta` adds cube containment and the maximal-isotropic condition on each `Alag v`. -/
structure GlobalDatum (P : CoverPackage D S H A) where
  T : ∀ v : FinPlace F, TorusRep D H v
  B : ∀ v : FinPlace F, v ∉ S.Sf → TameTorusBasis (T v)
  Alag : ∀ v : FinPlace F, Subgroup (v.adicCompletion F)ˣ
  alag_cubes : ∀ v (t : (v.adicCompletion F)ˣ), t ^ 3 ∈ Alag v
  alag_lagrangian : ∀ v (x : (v.adicCompletion F)ˣ),
    x ∈ Alag v ↔ ∀ y ∈ Alag v, torusPairing D H v x y = 1
  lam : ∀ v : FinPlace F, (T v).V →ₗ[ℂ] ℂ
  ω : ∀ v : FinPlace F, (v.adicCompletion F)ˣ → ℂ
  lam_equiv : ∀ v, ∀ y ∈ Alag v, ∀ x, lam v ((T v).σa y x) = ω v y * lam v x
  lam_ne : ∀ v, lam v ≠ 0
  alag_tame : ∀ v, v ∉ S.Sf → ∀ y : (v.adicCompletion F)ˣ,
    y ∈ Alag v ↔ ∃ (k : ℤ) (u : (v.adicCompletion F)ˣ), IsLocUnit v u ∧ y = unifLoc v ^ (3 * k) * u
  ω_tame : ∀ v, v ∉ S.Sf → ∀ y ∈ Alag v, ω v y = 1
  lam_tame : ∀ v (hv : v ∉ S.Sf) (k : ZMod 3), lam v ((B v hv).e k) = if k = 0 then 1 else 0
  ω_rational : ∀ δ : Fˣ, (∀ v, toLoc v δ ∈ Alag v) → ∏ v ∈ S.Sf, ω v (toLoc v δ) = 1

/-- The rational subgroup `Δ = {δ ∈ F^× : δ ∈ Alag v for all v}`. -/
def GlobalDatum.Δ {P : CoverPackage D S H A} (G : GlobalDatum P) : Subgroup Fˣ :=
  ⨅ v : FinPlace F, (G.Alag v).comap (toLoc v)

/-- Choose the exceptional or tame local model at each finite place. -/
theorem globalLocal_models (hSt : ∀ v, SteinbergAt H v) :
    ∀ v : FinPlace F, Nonempty (GlobalLocalModel D H v (v ∉ S.Sf)) := by
  intro v
  by_cases hv : v ∈ S.Sf
  · obtain ⟨L, hc, hl⟩ := globalLocal_lagrangian D H v
    obtain ⟨M, _⟩ := globalLocal_wild_model D H v L hc hl
    simpa only [hv, not_true_eq_false] using
      (show Nonempty (GlobalLocalModel D H v False) from ⟨M⟩)
  · simpa only [hv, not_false_eq_true] using
      globalLocal_tame_model D H v (hSt v) (fun h => hv (S.over6 v h))

/-- **eis:global-datum** (existence). The strengthened datum is required by C6 of
`sol-gate-theta`. -/
theorem exists_globalDatum (P : CoverPackage D S H A) (hSt : ∀ v, SteinbergAt H v) :
    Nonempty (GlobalDatum P) := by
  classical
  let M : ∀ v, GlobalLocalModel D H v (v ∉ S.Sf) :=
    fun v => Classical.choice (globalLocal_models hSt v)
  exact ⟨{
    T := fun v => (M v).T
    B := fun v hv => (M v).B hv
    Alag := fun v => (M v).Alag
    alag_cubes := fun v => (M v).cubes
    alag_lagrangian := fun v => (M v).lagrangian
    lam := fun v => (M v).lam
    ω := fun _ _ => 1
    lam_equiv := by intro v y hy x; simpa using (M v).lam_fixed y hy x
    lam_ne := fun v => (M v).lam_ne
    alag_tame := fun v hv => (M v).alag_tame hv
    ω_tame := by intros; rfl
    lam_tame := fun v hv => (M v).lam_tame hv
    ω_rational := by intros; simp
  }⟩

/-- **def:global-section**: a factorizable section of `I(σ_𝔸, s)`, spherical outside `T0 ⊇ S_f`.
Corrected per rev-theta to include archimedean smoothness along the root subgroups; C11 of
`sol-gate-theta` adds joint smoothness in both root variables. -/
structure GlobalSection (P : CoverPackage D S H A) (G : GlobalDatum P) (s : ℂ) where
  T0 : Finset (FinPlace F)
  sub : S.Sf ⊆ T0
  f : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V
  f_sec : ∀ v, IsSection (P.loc v) (G.T v) s (f v)
  f_sph : ∀ v (hv : v ∉ T0), f v 1 = (G.B v (fun h => hv (sub h))).e 0 ∧
    ∀ g, ∀ k ∈ (P.tame v (fun h => hv (sub h))).Kmax, f v (g * k) = f v g
  fC : InfinitePlace F → PGL2 ℂ → ℂ
  fC_sec : ∀ w, IsSectionC s (fC w) ∧ Continuous (fC w)
  fC_smooth : ∀ w (g : PGL2 ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => fC w (g * nC z))
  fC_jointSmooth : ∀ w (g : PGL2 ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℂ => fC w (nC p.1 * g * nC p.2))

/-- **def:scalar-section**: `Φ(q x) = Π_v lam_v(f_v(x_v)) · Π_w f_w(x_w)` (independent of the lift `x`). -/
def scalarOf (P : CoverPackage D S H A) (G : GlobalDatum P)
    (fv : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V) (fc : InfinitePlace F → PGL2 ℂ → ℂ)
    (g : P.tc.G) : ℂ :=
  (∏ᶠ v, G.lam v (fv v (P.compF v (Function.surjInv P.q_surj g)))) *
    ∏ w, fc w (P.compC w (Function.surjInv P.q_surj g))

/-- **eis:scalar-well-defined**: the formula at any lift, with finite support. -/
theorem scalarOf_q (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (Fs : GlobalSection P G s) (x : P.RP) :
    (Function.mulSupport fun v => G.lam v (Fs.f v (P.compF v x))).Finite ∧
    scalarOf P G Fs.f Fs.fC (P.q x) =
      (∏ᶠ v, G.lam v (Fs.f v (P.compF v x))) * ∏ w, Fs.fC w (P.compC w x) := by
  classical
  have hfinite (r : P.RP) :
      (Function.mulSupport fun v => G.lam v (Fs.f v (P.compF v r))).Finite := by
    let bad : Set (FinPlace F) :=
      {v | ∃ hv : v ∉ S.Sf, P.compF v r ∉ (P.tame v hv).Kmax}
    have hbad : bad.Finite := P.comp_restricted r
    apply Set.Finite.subset (Fs.T0.finite_toSet.union hbad)
    intro v hv
    by_contra hvout
    have hvT : v ∉ Fs.T0 := by
      intro h
      exact hvout (Or.inl h)
    have hvS : v ∉ S.Sf := fun h => hvT (Fs.sub h)
    have hK : P.compF v r ∈ (P.tame v hvS).Kmax := by
      by_contra hK
      exact hvout (Or.inr ⟨hvS, hK⟩)
    rcases Fs.f_sph v hvT with ⟨h1, hKinv⟩
    have hf : Fs.f v (P.compF v r) = (G.B v hvS).e 0 := by
      calc
        Fs.f v (P.compF v r) = Fs.f v (1 * P.compF v r) := by simp
        _ = Fs.f v 1 := hKinv 1 (P.compF v r) hK
        _ = (G.B v hvS).e 0 := h1
    have hlam : G.lam v (Fs.f v (P.compF v r)) = 1 := by
      rw [hf]
      simpa using G.lam_tame v hvS 0
    exact hv hlam
  let y : P.RP := Function.surjInv P.q_surj (P.q x)
  have hq : P.q x = P.q y := by
    exact (Function.rightInverse_surjInv P.q_surj (P.q x)).symm
  obtain ⟨ζ, hζfin, hζprod, hcomp, hcompC⟩ := (P.q_eq x y).mp hq
  let α : FinPlace F → ℂ := fun v => G.lam v (Fs.f v (P.compF v x))
  let β : FinPlace F → ℂ := fun v => G.lam v (Fs.f v (P.compF v y))
  have hrel : α = fun v => ((ζ v : ℂˣ) : ℂ) * β v := by
    funext v
    dsimp [α, β]
    have hf : Fs.f v (P.compF v x) =
        ((ζ v : ℂˣ) : ℂ) • Fs.f v (P.compF v y) := by
      rw [hcomp v]
      exact (Fs.f_sec v).2.1 (ζ v) (P.compF v y)
    rw [hf]
    simp
  let s : Finset (FinPlace F) :=
    hζfin.toFinset ∪ (hfinite x).toFinset ∪ (hfinite y).toFinset
  have hζone : ∀ v, v ∉ s → ζ v = 1 := by
    intro v hv
    apply (Function.notMem_mulSupport).mp
    intro hvζ
    have hvζ' : v ∈ hζfin.toFinset := (hζfin.mem_toFinset).mpr hvζ
    apply hv
    simp [s, hvζ']
  have hαone : ∀ v, v ∉ s → α v = 1 := by
    intro v hv
    apply (Function.notMem_mulSupport).mp
    intro hvα
    have hvα' : v ∈ (hfinite x).toFinset :=
      ((hfinite x).mem_toFinset).mpr (by simpa [α] using hvα)
    apply hv
    simp [s, hvα']
  have hβone : ∀ v, v ∉ s → β v = 1 := by
    intro v hv
    apply (Function.notMem_mulSupport).mp
    intro hvβ
    have hvβ' : v ∈ (hfinite y).toFinset :=
      ((hfinite y).mem_toFinset).mpr (by simpa [β] using hvβ)
    apply hv
    simp [s, hvβ']
  have hζfiniteProd : ∏ v ∈ s, ζ v = 1 := by
    calc
      ∏ v ∈ s, ζ v = ∏ᶠ v, ζ v := (finprod_eq_prod_of_mulSupport_subset ζ
        (Function.mulSupport_subset_iff'.2 hζone)).symm
      _ = 1 := hζprod
  have hζscalarProd : ∏ v ∈ s, ((ζ v : ℂˣ) : ℂ) = 1 := by
    let eval : rootsOfUnity 3 ℂ →* ℂ :=
      { toFun := fun z => ((z : ℂˣ) : ℂ)
        map_one' := rfl
        map_mul' := by intros; rfl }
    have hcoe := congrArg eval hζfiniteProd
    have hmap : eval (∏ v ∈ s, ζ v) = ∏ v ∈ s, ((ζ v : ℂˣ) : ℂ) := by
      simp [eval]
    calc
      ∏ v ∈ s, ((ζ v : ℂˣ) : ℂ) = eval (∏ v ∈ s, ζ v) := hmap.symm
      _ = eval 1 := hcoe
      _ = 1 := by simp [eval]
  have hαprod : (∏ᶠ v, α v) = ∏ᶠ v, β v := by
    rw [finprod_eq_prod_of_mulSupport_subset α (Function.mulSupport_subset_iff'.2 hαone),
      finprod_eq_prod_of_mulSupport_subset β (Function.mulSupport_subset_iff'.2 hβone)]
    rw [show (∏ v ∈ s, α v) = ∏ v ∈ s, (((ζ v : ℂˣ) : ℂ) * β v) by
      simp_rw [hrel]]
    rw [Finset.prod_mul_distrib, hζscalarProd, one_mul]
  refine ⟨hfinite x, ?_⟩
  change (∏ᶠ v, β v) * (∏ w, Fs.fC w (P.compC w y)) =
    (∏ᶠ v, α v) * (∏ w, Fs.fC w (P.compC w x))
  rw [hαprod]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  exact (congrArg (Fs.fC w) (hcompC w)).symm

/-- `B_*(F) = {b upper triangular : b₁₁/b₂₂ ∈ Δ}`. -/
def Bstar {P : CoverPackage D S H A} (G : GlobalDatum P) : Subgroup (GL (Fin 2) F) where
  carrier := {b | (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
    ∃ δ ∈ G.Δ, (b : Matrix (Fin 2) (Fin 2) F) 0 0 = (δ : F) * (b : Matrix (Fin 2) (Fin 2) F) 1 1}
  one_mem' := by
    refine ⟨by simp, 1, one_mem _, ?_⟩
    simp
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨ha10, δ, hδ, ha00⟩
    rcases hb with ⟨hb10, δ', hδ', hb00⟩
    refine ⟨?_, δ * δ', G.Δ.mul_mem hδ hδ', ?_⟩
    · change ((a * b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      rw [ha10, hb10]
      ring
    · change ((a * b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        ((δ * δ' : Fˣ) : F) * ((a * b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      rw [ha10, hb10, ha00, hb00]
      ring
  inv_mem' := by
    intro b hb
    rcases hb with ⟨hb10, δ, hδ, hb00⟩
    let c : GL (Fin 2) F := b⁻¹
    have hbc : (b : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) = 1 := by
      have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
        (mul_inv_cancel b)
      simpa [c] using h
    have hbc10 : ((b : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0 := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hbc
      simpa using h
    have hbc00 : ((b : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F)) 0 0 = 1 := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hbc
      simpa using h
    have hbc11 : ((b : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F)) 1 1 = 1 := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hbc
      simpa using h
    have hb11ne : (b : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      intro hzero
      have hprod : (b : Matrix (Fin 2) (Fin 2) F) 1 1 * (c : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_two, hb10] using hbc11
      rw [hzero, zero_mul] at hprod
      norm_num at hprod
    have hc10 : (c : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have hprod : (b : Matrix (Fin 2) (Fin 2) F) 1 1 * (c : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_two, hb10] using hbc10
      exact (mul_eq_zero.mp hprod).resolve_left hb11ne
    have hb00c00 : (b : Matrix (Fin 2) (Fin 2) F) 0 0 *
        (c : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hc10] using hbc00
    have hb11c11 : (b : Matrix (Fin 2) (Fin 2) F) 1 1 *
        (c : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hb10] using hbc11
    have hc00inv : (c : Matrix (Fin 2) (Fin 2) F) 0 0 =
        ((b : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hb00c00)
    have hc11inv : (c : Matrix (Fin 2) (Fin 2) F) 1 1 =
        ((b : Matrix (Fin 2) (Fin 2) F) 1 1)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hb11c11)
    refine ⟨hc10, δ⁻¹, G.Δ.inv_mem hδ, ?_⟩
    change (c : Matrix (Fin 2) (Fin 2) F) 0 0 =
      ((δ⁻¹ : Fˣ) : F) * (c : Matrix (Fin 2) (Fin 2) F) 1 1
    rw [hc00inv, hc11inv, hb00]
    simp [mul_inv_rev, mul_comm]

private theorem bstar_factorization {P : CoverPackage D S H A} (G : GlobalDatum P)
    (b : GL (Fin 2) F) (hb : b ∈ Bstar G) :
    ∃ c : Fˣ, ∃ δ ∈ G.Δ, ∃ x : F,
      b = scalarGL c * (upperGL x * diagGL δ) := by
  rcases hb with ⟨hb10, δ, hδ, hb00⟩
  have hb11ne : (b : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    let c : GL (Fin 2) F := b⁻¹
    have hbc : (b : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) = 1 := by
      have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F))
        (mul_inv_cancel b)
      simpa [c] using h
    have hbc11 : ((b : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F)) 1 1 = 1 := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hbc
      simpa using h
    have hprod : (b : Matrix (Fin 2) (Fin 2) F) 1 1 *
        (c : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hb10] using hbc11
    intro hz
    rw [hz, zero_mul] at hprod
    norm_num at hprod
  let c : Fˣ := Units.mk0 ((b : Matrix (Fin 2) (Fin 2) F) 1 1) hb11ne
  let x : F := (b : Matrix (Fin 2) (Fin 2) F) 0 1 /
    (b : Matrix (Fin 2) (Fin 2) F) 1 1
  have hmat : b = scalarGL c * (upperGL x * diagGL δ) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [c, x, scalarGL, upperGL, diagGL, Matrix.mul_apply, Fin.sum_univ_two,
        hb10, hb00] <;> field_simp [hb11ne] <;> ring
  exact ⟨c, δ, hδ, x, hmat⟩

private theorem scalarOf_lift_components {P : CoverPackage D S H A} {G : GlobalDatum P}
    {s : ℂ} (Fs : GlobalSection P G s) (x y : P.RP)
    (hF : ∀ v, G.lam v (Fs.f v (P.compF v x)) = G.lam v (Fs.f v (P.compF v y)))
    (hC : ∀ w, Fs.fC w (P.compC w x) = Fs.fC w (P.compC w y)) :
    scalarOf P G Fs.f Fs.fC (P.q x) = scalarOf P G Fs.f Fs.fC (P.q y) := by
  rw [(scalarOf_q P G Fs x).2, (scalarOf_q P G Fs y).2]
  congr 1
  · apply finprod_congr
    intro v
    exact hF v
  · apply Finset.prod_congr rfl
    intro w hw
    exact hC w

private theorem scalar_upperM_zero {K : Type} [Field K] : upperM K (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperM]

private theorem scalar_diagM_one {K : Type} [Field K] : diagM K (1 : Kˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagM]

private theorem scalarOf_nS_invariance (P : CoverPackage D S H A)
    (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s)
    (x : S.FS) (g : P.tc.G) :
    scalarOf P G Fs.f Fs.fC (P.tc.nS (Multiplicative.ofAdd x) * g) =
      scalarOf P G Fs.f Fs.fC g := by
  classical
  obtain ⟨r, hqr, hFr, hCr⟩ := P.nS_components x
  obtain ⟨y, hqy⟩ := P.q_surj g
  have hqmul : P.q (r * y) = P.tc.nS (Multiplicative.ofAdd x) * g := by
    rw [(P.q).map_mul, hqr, hqy]
  rw [← hqmul, ← hqy]
  apply scalarOf_lift_components Fs (r * y) y
  · intro v
    rw [(P.compF v).map_mul, hFr v]
    by_cases hv : v ∈ S.Sf
    · simp only [dif_pos hv]
      have hloc : Fs.f v ((P.loc v).n (Multiplicative.ofAdd (x.1 ⟨v, hv⟩)) *
          P.compF v y) = Fs.f v (P.compF v y) := by
        have hs := (Fs.f_sec v).1 (x.1 ⟨v, hv⟩) 1 (P.compF v y)
        simpa [(P.loc v).a_one, (G.T v).σa_one, absFin_eq_norm] using hs
      rw [hloc]
    · simp [hv]
  · intro w
    rw [(P.compC w).map_mul, hCr w]
    have hs := (Fs.fC_sec w).1 (x.2 w) 1 (P.compC w y)
    simpa [scalar_upperM_zero, scalar_diagM_one] using hs

private theorem scalarOf_n_invariance (P : CoverPackage D S H A)
    (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s)
    (v : FinPlace F) (hv : v ∉ S.Sf) (x : Multiplicative (v.adicCompletion F))
    (g : P.tc.G) :
    scalarOf P G Fs.f Fs.fC (P.tc.n v x * g) = scalarOf P G Fs.f Fs.fC g := by
  classical
  let r : P.RP := P.incl v ((P.loc v).n x)
  obtain ⟨y, hqy⟩ := P.q_surj g
  have hqr : P.q r = P.tc.n v x := by
    dsimp [r]
    rw [P.q_incl, P.emb_n v hv]
  have hqmul : P.q (r * y) = P.tc.n v x * g := by
    rw [(P.q).map_mul, hqr, hqy]
  rw [← hqmul, ← hqy]
  apply scalarOf_lift_components Fs (r * y) y
  · intro u
    rw [(P.compF u).map_mul]
    by_cases huv : u = v
    · subst u
      rw [P.incl_compF]
      have hs := (Fs.f_sec v).1 (Multiplicative.toAdd x) 1 (P.compF v y)
      have hloc : Fs.f v ((P.loc v).n x * P.compF v y) = Fs.f v (P.compF v y) := by
        simpa [(P.loc v).a_one, (G.T v).σa_one, absFin_eq_norm] using hs
      rw [hloc]
    · rw [P.incl_compF_other v u (Ne.symm huv)]
      simp
  · intro w
    rw [(P.compC w).map_mul, P.incl_compC]
    have hs := (Fs.fC_sec w).1 0 1 (P.compC w y)
    simpa [scalar_upperM_zero, scalar_diagM_one] using hs

private theorem scalarOf_z_invariance_at (P : CoverPackage D S H A)
    (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s)
    (v : FinPlace F) (ζ : rootsOfUnity 3 ℂ) (g : P.tc.G) :
    scalarOf P G Fs.f Fs.fC (P.tc.z ζ * g) =
      ((ζ : ℂˣ) : ℂ) * scalarOf P G Fs.f Fs.fC g := by
  classical
  let r : P.RP := P.incl v ((P.loc v).z ζ)
  obtain ⟨y, hqy⟩ := P.q_surj g
  have hqr : P.q r = P.tc.z ζ := by
    dsimp [r]
    rw [P.q_incl, P.emb_z]
  have hqmul : P.q (r * y) = P.tc.z ζ * g := by
    rw [(P.q).map_mul, hqr, hqy]
  let α : FinPlace F → ℂ := fun u => G.lam u (Fs.f u (P.compF u y))
  let β : FinPlace F → ℂ := fun u => G.lam u (Fs.f u (P.compF u (r * y)))
  let χ : FinPlace F → ℂ := fun u => if u = v then ((ζ : ℂˣ) : ℂ) else 1
  have hβα : ∀ u, β u = χ u * α u := by
    intro u
    change G.lam u (Fs.f u (P.compF u (r * y))) = χ u * α u
    rw [(P.compF u).map_mul]
    by_cases huv : u = v
    · subst u
      rw [P.incl_compF]
      have hs := (Fs.f_sec v).2.1 ζ (P.compF v y)
      rw [hs]
      simp [χ, α, map_smul]
    · rw [P.incl_compF_other v u (Ne.symm huv)]
      simp [χ, α, huv]
  have hχfinite : Function.HasFiniteMulSupport χ := by
    change (Function.mulSupport χ).Finite
    apply Set.Finite.subset (Set.finite_singleton v)
    intro u hu
    by_contra huv
    have hneq : u ≠ v := by simpa [Finset.mem_singleton] using huv
    have hχ : χ u = 1 := by simp [χ, hneq]
    exact (Function.mem_mulSupport.mp hu) hχ
  have hαfinite : Function.HasFiniteMulSupport α := (scalarOf_q P G Fs y).1
  have hβfinite : Function.HasFiniteMulSupport β := (scalarOf_q P G Fs (r * y)).1
  have hβprod : (∏ᶠ u, β u) = (∏ᶠ u, χ u) * ∏ᶠ u, α u := by
    have hfun : β = fun u => χ u * α u := funext hβα
    rw [hfun]
    exact finprod_mul_distrib hχfinite hαfinite
  have hχprod : (∏ᶠ u, χ u) = ((ζ : ℂˣ) : ℂ) := by
    have hout : ∀ u, u ∉ ({v} : Finset (FinPlace F)) → χ u = 1 := by
      intro u hu
      have hneq : u ≠ v := by simpa [Finset.mem_singleton] using hu
      simp [χ, hneq]
    rw [finprod_eq_prod_of_mulSupport_subset χ (Function.mulSupport_subset_iff'.2 hout)]
    simp [χ]
  have hC : ∀ w, Fs.fC w (P.compC w (r * y)) = Fs.fC w (P.compC w y) := by
    intro w
    rw [(P.compC w).map_mul, P.incl_compC]
    have hs := (Fs.fC_sec w).1 0 1 (P.compC w y)
    simpa using hs
  have harch : (∏ w, Fs.fC w (P.compC w (r * y))) =
      ∏ w, Fs.fC w (P.compC w y) := by
    apply Finset.prod_congr rfl
    intro w hw
    exact hC w
  rw [← hqmul, ← hqy, (scalarOf_q P G Fs (r * y)).2, (scalarOf_q P G Fs y).2]
  rw [hβprod, hχprod, harch]
  ring

private theorem scalar_nonempty_finPlace : Nonempty (FinPlace F) := by
  letI : IsDedekindDomain (𝓞 F) := inferInstance
  have hnot : ¬ IsField (𝓞 F) := NumberField.RingOfIntegers.not_isField F
  rcases (Ring.not_isField_iff_exists_prime (R := 𝓞 F)).mp hnot with ⟨I, hI0, hI⟩
  exact ⟨⟨I, hI, hI0⟩⟩

private theorem complexOfReal_cpow_finset_prod {ι : Type} [DecidableEq ι]
    (t : Finset ι) (a : ι → ℝ) (p : ℂ) (ha : ∀ i ∈ t, 0 ≤ a i) :
    ((∏ i ∈ t, a i : ℝ) : ℂ) ^ p = ∏ i ∈ t, ((a i : ℝ) : ℂ) ^ p := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih =>
    have hprod : 0 ≤ ∏ j ∈ t, a j :=
      Finset.prod_nonneg (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hit, Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (ha i (by simp)) hprod p]
    rw [ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))]
    simp [Finset.prod_insert, hit]

private theorem scalar_abs_product_formula (D : FieldData F) (δ : Fˣ) :
    (∏ᶠ v : FinPlace F, absFin v (toLoc v δ)) *
      ∏ w : InfinitePlace F, Complex.normSq (w.embedding (δ : F)) = 1 := by
  letI : IsTotallyComplex F := D.isTotallyComplex
  have hfinite : (∏ᶠ v : FinPlace F, absFin v (toLoc v δ)) =
      ∏ᶠ v : FinitePlace F, v (δ : F) := by
    calc
      ∏ᶠ v : FinPlace F, absFin v (toLoc v δ) =
          ∏ᶠ v : FinPlace F, ‖FinitePlace.embedding v (δ : F)‖ := by
        apply finprod_congr
        intro v
        simpa [toLoc] using absFin_algebraMap v (δ : F)
      _ = ∏ᶠ v : FinitePlace F, v (δ : F) := by
        rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
        apply finprod_congr
        intro v
        simp [FinitePlace.equivHeightOneSpectrum_symm_apply]
  have harch : (∏ w : InfinitePlace F, Complex.normSq (w.embedding (δ : F))) =
      ∏ w : InfinitePlace F, w (δ : F) ^ w.mult := by
    apply Finset.prod_congr rfl
    intro w hw
    exact normSq_embedding_eq w (δ : F)
  have hprod := prod_abs_eq_one (Units.ne_zero δ)
  calc
    (∏ᶠ v : FinPlace F, absFin v (toLoc v δ)) *
        ∏ w : InfinitePlace F, Complex.normSq (w.embedding (δ : F)) =
      (∏ᶠ v : FinitePlace F, v (δ : F)) *
        ∏ w : InfinitePlace F, w (δ : F) ^ w.mult := by rw [hfinite, harch]
    _ = (∏ w : InfinitePlace F, w (δ : F) ^ w.mult) *
        ∏ᶠ v : FinitePlace F, v (δ : F) := by ac_rfl
    _ = 1 := hprod

private theorem scalar_abs_cpow_product (D : FieldData F) (δ : Fˣ) (p : ℂ) :
    (∏ᶠ v : FinPlace F, ((absFin v (toLoc v δ) : ℝ) : ℂ) ^ p) *
      ∏ w : InfinitePlace F,
        ((Complex.normSq (w.embedding (δ : F)) : ℝ) : ℂ) ^ p = 1 := by
  classical
  let A : FinPlace F → ℝ := fun v => absFin v (toLoc v δ)
  let B : InfinitePlace F → ℝ := fun w => Complex.normSq (w.embedding (δ : F))
  have hnorm : Function.HasFiniteMulSupport
      (fun v : FinPlace F => ‖FinitePlace.embedding v (δ : F)‖) := by
    simpa using finitePlace_mk_hasFiniteMulSupport (Units.ne_zero δ)
  have hAeq (v : FinPlace F) : A v = ‖FinitePlace.embedding v (δ : F)‖ := by
    simpa [A, toLoc] using absFin_algebraMap v (δ : F)
  have hAfinite : Function.HasFiniteMulSupport A := by
    change (Function.mulSupport A).Finite
    rw [show A = fun v : FinPlace F => ‖FinitePlace.embedding v (δ : F)‖ from funext hAeq]
    exact hnorm
  have hA_nonneg (v : FinPlace F) : 0 ≤ A v := by
    dsimp [A, absFin]
    split_ifs <;> positivity
  have hB_nonneg (w : InfinitePlace F) : 0 ≤ B w := by
    exact Complex.normSq_nonneg _
  let α : FinPlace F → ℂ := fun v => ((A v : ℝ) : ℂ) ^ p
  let t := hAfinite.toFinset
  have hAout : ∀ v, v ∉ t → A v = 1 := by
    intro v hv
    apply Function.notMem_mulSupport.mp
    intro h
    apply hv
    simpa [t] using hAfinite.mem_toFinset.mpr h
  have hαout : ∀ v, v ∉ t → α v = 1 := by
    intro v hv
    simp [α, hAout v hv]
  have hfinite_cpow : (∏ᶠ v : FinPlace F, α v) =
      ((∏ᶠ v : FinPlace F, A v : ℝ) : ℂ) ^ p := by
    rw [finprod_eq_prod_of_mulSupport_subset α (Function.mulSupport_subset_iff'.2 hαout),
      finprod_eq_prod_of_mulSupport_subset A (Function.mulSupport_subset_iff'.2 hAout)]
    exact (complexOfReal_cpow_finset_prod t A p (fun v hv => hA_nonneg v)).symm
  have harch_cpow : (∏ w : InfinitePlace F, ((B w : ℝ) : ℂ) ^ p) =
      ((∏ w : InfinitePlace F, B w : ℝ) : ℂ) ^ p := by
    exact (complexOfReal_cpow_finset_prod Finset.univ B p (fun w hw => hB_nonneg w)).symm
  have hbase := scalar_abs_product_formula D δ
  rw [show ∏ᶠ v : FinPlace F, α v =
        (∏ᶠ v : FinPlace F, ((absFin v (toLoc v δ) : ℝ) : ℂ) ^ p) from by
          apply finprod_congr; intro v; rfl] at hfinite_cpow
  rw [show ∏ w : InfinitePlace F, ((B w : ℝ) : ℂ) ^ p =
        ∏ w : InfinitePlace F,
          ((Complex.normSq (w.embedding (δ : F)) : ℝ) : ℂ) ^ p from by
          apply Finset.prod_congr rfl; intro w hw; rfl] at harch_cpow
  rw [hfinite_cpow, harch_cpow]
  have hfinbase_nonneg : 0 ≤ ∏ᶠ v : FinPlace F, A v := by
    rw [show (∏ᶠ v : FinPlace F, A v) = ∏ v ∈ t, A v from
      finprod_eq_prod_of_mulSupport_subset A (Function.mulSupport_subset_iff'.2 hAout)]
    exact Finset.prod_nonneg (fun v hv => hA_nonneg v)
  have harchbase_nonneg : 0 ≤ ∏ w : InfinitePlace F, B w :=
    Finset.prod_nonneg (fun w hw => hB_nonneg w)
  rw [← Complex.mul_cpow_ofReal_nonneg hfinbase_nonneg harchbase_nonneg p,
    ← Complex.ofReal_mul, hbase]
  simp

private theorem scalar_glMap_diagGL {K : Type} [Field K] (φ : F →+* K) (δ : Fˣ) :
    Matrix.GeneralLinearGroup.map φ (diagGL δ) =
      diagM K (Units.map φ.toMonoidHom δ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL, diagM]

private theorem scalar_glMap_upperGL {K : Type} [Field K] (φ : F →+* K) (x : F) :
    Matrix.GeneralLinearGroup.map φ (upperGL x) = upperM K (φ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperGL, upperM]

private theorem scalar_delta_mem_iff {P : CoverPackage D S H A} (G : GlobalDatum P)
    (δ : Fˣ) : δ ∈ G.Δ ↔ ∀ v, toLoc v δ ∈ G.Alag v := by
  simp [GlobalDatum.Δ]

private theorem scalarOf_diag_invariance (P : CoverPackage D S H A)
    (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s)
    (δ : Fˣ) (hδ : δ ∈ G.Δ) (g : P.tc.G) :
    scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL δ) * g) =
      scalarOf P G Fs.f Fs.fC g := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let p : ℂ := (1 : ℂ) / 2 + s
  let A : FinPlace F → ℝ := fun v => absFin v (toLoc v δ)
  let amp : FinPlace F → ℂ := fun v => ((A v : ℝ) : ℂ) ^ p
  let omega : FinPlace F → ℂ := fun v => G.ω v (toLoc v δ)
  let weight : FinPlace F → ℂ := fun v => amp v * omega v
  let archAmp : InfinitePlace F → ℂ := fun w =>
    ((Complex.normSq (w.embedding (δ : F)) : ℝ) : ℂ) ^ p
  let α : FinPlace F → ℂ := fun v => G.lam v (Fs.f v (P.compF v (Function.surjInv P.q_surj g)))
  let r : P.RP := P.ratRP (diagGL δ) * Function.surjInv P.q_surj g
  let β : FinPlace F → ℂ := fun v => G.lam v (Fs.f v (P.compF v r))
  let γ : InfinitePlace F → ℂ := fun w => Fs.fC w
    (P.compC w (Function.surjInv P.q_surj g))
  let γ' : InfinitePlace F → ℂ := fun w => Fs.fC w (P.compC w r)
  have hxq : P.q (Function.surjInv P.q_surj g) = g := by
    exact Function.rightInverse_surjInv P.q_surj g
  have hrq : P.q r = P.tc.rat (diagGL δ) * g := by
    dsimp [r]
    rw [(P.q).map_mul, P.q_ratRP, hxq]
  have hδloc : ∀ v, toLoc v δ ∈ G.Alag v :=
    (scalar_delta_mem_iff G δ).mp hδ
  have hcompF (v : FinPlace F) : P.compF v r =
      (P.loc v).a (toLoc v δ) * P.compF v (Function.surjInv P.q_surj g) := by
    dsimp [r]
    rw [(P.compF v).map_mul, P.compF_ratRP, scalar_glMap_diagGL,
      (P.loc v).sec_a]
    simp [toLoc]
  have hcompC (w : InfinitePlace F) : P.compC w r =
      QuotientGroup.mk (diagM ℂ (Units.map w.embedding.toMonoidHom δ)) *
        P.compC w (Function.surjInv P.q_surj g) := by
    dsimp [r]
    rw [(P.compC w).map_mul, P.compC_ratRP, scalar_glMap_diagGL]
    rfl
  have hβα : ∀ v, β v = weight v * α v := by
    intro v
    dsimp [β, α]
    rw [hcompF v]
    have hs := (Fs.f_sec v).1 0 (toLoc v δ)
      (P.compF v (Function.surjInv P.q_surj g))
    have hloc : Fs.f v ((P.loc v).a (toLoc v δ) *
        P.compF v (Function.surjInv P.q_surj g)) =
        ((absFin v (toLoc v δ) : ℂ) ^ p) •
          (G.T v).σa (toLoc v δ)
            (Fs.f v (P.compF v (Function.surjInv P.q_surj g))) := by
      simpa [p] using hs
    rw [hloc, map_smul, G.lam_equiv v (toLoc v δ) (hδloc v)]
    simp only [weight, amp, omega, A, p]
    ring
  have hγα : ∀ w, γ' w = archAmp w * γ w := by
    intro w
    dsimp [γ', γ]
    rw [hcompC w]
    have hs := (Fs.fC_sec w).1 0 (Units.map w.embedding.toMonoidHom δ)
      (P.compC w (Function.surjInv P.q_surj g))
    simpa [scalar_upperM_zero, archAmp, p] using hs
  have hαfinite : Function.HasFiniteMulSupport α := by
    dsimp [α]
    exact (scalarOf_q P G Fs (Function.surjInv P.q_surj g)).1
  have hβfinite : Function.HasFiniteMulSupport β := by
    dsimp [β]
    exact (scalarOf_q P G Fs r).1
  have hAfinite : Function.HasFiniteMulSupport A := by
    have hn : Function.HasFiniteMulSupport
        (fun v : FinPlace F => ‖FinitePlace.embedding v (δ : F)‖) := by
      simpa using finitePlace_mk_hasFiniteMulSupport (Units.ne_zero δ)
    have hEq : A = fun v : FinPlace F => ‖FinitePlace.embedding v (δ : F)‖ := by
      funext v
      simpa [A, toLoc] using absFin_algebraMap v (δ : F)
    change (Function.mulSupport A).Finite
    rw [hEq]
    exact hn
  have hAmpfinite : Function.HasFiniteMulSupport amp := by
    have hsub : Function.mulSupport amp ⊆ Function.mulSupport A := by
      intro v hv
      by_contra hvA
      have hAone : A v = 1 := Function.notMem_mulSupport.mp hvA
      exact (Function.mem_mulSupport.mp hv) (by simp [amp, hAone])
    change (Function.mulSupport amp).Finite
    exact hAfinite.subset hsub
  have homegaOut : ∀ v, v ∉ S.Sf → omega v = 1 := by
    intro v hv
    exact G.ω_tame v hv (toLoc v δ) (hδloc v)
  have homegafinite : Function.HasFiniteMulSupport omega := by
    change (Function.mulSupport omega).Finite
    apply Set.Finite.subset S.Sf.finite_toSet
    intro v hv
    by_contra hvS
    exact (Function.mem_mulSupport.mp hv) (homegaOut v hvS)
  have hweightfinite : Function.HasFiniteMulSupport weight :=
    hAmpfinite.mul homegafinite
  have hweightprod : (∏ᶠ v, weight v) * ∏ w, archAmp w = 1 := by
    have homegaprod : (∏ᶠ v, omega v) = 1 := by
      rw [finprod_eq_prod_of_mulSupport_subset omega
        (Function.mulSupport_subset_iff'.2 homegaOut)]
      exact G.ω_rational δ hδloc
    have hlocalprod : (∏ᶠ v, weight v) =
        (∏ᶠ v, amp v) * ∏ᶠ v, omega v := by
      change (∏ᶠ v, amp v * omega v) = _
      exact finprod_mul_distrib hAmpfinite homegafinite
    calc
      (∏ᶠ v, weight v) * ∏ w, archAmp w =
          ((∏ᶠ v, amp v) * ∏ᶠ v, omega v) * ∏ w, archAmp w := by rw [hlocalprod]
      _ = (∏ᶠ v, amp v) * ∏ w, archAmp w := by rw [homegaprod]; ring
      _ = 1 := scalar_abs_cpow_product D δ p
  have hβprod : (∏ᶠ v, β v) = (∏ᶠ v, weight v) * ∏ᶠ v, α v := by
    have hfun : β = fun v => weight v * α v := funext hβα
    rw [hfun]
    exact finprod_mul_distrib hweightfinite hαfinite
  have harchprod : (∏ w, γ' w) = (∏ w, archAmp w) * ∏ w, γ w := by
    calc
      ∏ w, γ' w = ∏ w, archAmp w * γ w := by
        apply Finset.prod_congr rfl
        intro w hw
        exact hγα w
      _ = (∏ w, archAmp w) * ∏ w, γ w := Finset.prod_mul_distrib
  rw [← hrq, ← hxq, (scalarOf_q P G Fs r).2,
    (scalarOf_q P G Fs (Function.surjInv P.q_surj g)).2]
  rw [hβprod, harchprod]
  calc
    ((∏ᶠ v, weight v) * ∏ᶠ v, α v) *
        ((∏ w, archAmp w) * ∏ w, γ w) =
      ((∏ᶠ v, weight v) * ∏ w, archAmp w) *
        ((∏ᶠ v, α v) * ∏ w, γ w) := by ring
    _ = 1 * ((∏ᶠ v, α v) * ∏ w, γ w) := by rw [hweightprod]
    _ = (∏ᶠ v, α v) * ∏ w, γ w := by ring

private theorem scalarOf_upper_rat_invariance (P : CoverPackage D S H A)
    (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s)
    (x : F) (g : P.tc.G) :
    scalarOf P G Fs.f Fs.fC (P.tc.rat (upperGL x) * g) =
      scalarOf P G Fs.f Fs.fC g := by
  classical
  let r : P.RP := P.ratRP (upperGL x) * Function.surjInv P.q_surj g
  have hq : P.q (Function.surjInv P.q_surj g) = g :=
    Function.rightInverse_surjInv P.q_surj g
  have hrq : P.q r = P.tc.rat (upperGL x) * g := by
    dsimp [r]
    rw [(P.q).map_mul, P.q_ratRP, hq]
  have hcompF (v : FinPlace F) : P.compF v r =
      (P.loc v).n (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F) x)) *
        P.compF v (Function.surjInv P.q_surj g) := by
    dsimp [r]
    rw [(P.compF v).map_mul, P.compF_ratRP, scalar_glMap_upperGL,
      (P.loc v).sec_n]
  have hcompC (w : InfinitePlace F) : P.compC w r =
      QuotientGroup.mk (upperM ℂ (w.embedding x)) *
        P.compC w (Function.surjInv P.q_surj g) := by
    dsimp [r]
    rw [(P.compC w).map_mul, P.compC_ratRP, scalar_glMap_upperGL]
  rw [← hrq, ← hq]
  apply scalarOf_lift_components Fs r (Function.surjInv P.q_surj g)
  · intro v
    rw [hcompF v]
    have hs := (Fs.f_sec v).1 (algebraMap F (v.adicCompletion F) x) 1
      (P.compF v (Function.surjInv P.q_surj g))
    have hloc : Fs.f v ((P.loc v).n
        (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F) x)) *
        P.compF v (Function.surjInv P.q_surj g)) =
        Fs.f v (P.compF v (Function.surjInv P.q_surj g)) := by
      simpa [(P.loc v).a_one, (G.T v).σa_one, absFin_eq_norm] using hs
    rw [hloc]
  · intro w
    rw [hcompC w]
    have hs := (Fs.fC_sec w).1 (w.embedding x) 1
      (P.compC w (Function.surjInv P.q_surj g))
    simpa [scalar_upperM_zero, scalar_diagM_one] using hs

/-- **eis:left-inv**: `Φ` is left `B_*(F)`-invariant, left `N(F_S)`- and `N(K_v)`-invariant, and
genuine. -/
theorem scalarOf_invariance (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (Fs : GlobalSection P G s) :
    (∀ b ∈ Bstar G, ∀ g, scalarOf P G Fs.f Fs.fC (P.tc.rat b * g) = scalarOf P G Fs.f Fs.fC g) ∧
    (∀ x g, scalarOf P G Fs.f Fs.fC (P.tc.nS x * g) = scalarOf P G Fs.f Fs.fC g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, scalarOf P G Fs.f Fs.fC (P.tc.n v x * g) = scalarOf P G Fs.f Fs.fC g) ∧
    (∀ ζ g, scalarOf P G Fs.f Fs.fC (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * scalarOf P G Fs.f Fs.fC g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb g
    obtain ⟨c, δ, hδ, x, hfactor⟩ := bstar_factorization G b hb
    have harg : P.tc.rat b * g = P.tc.rat (scalarGL c) *
        (P.tc.rat (upperGL x) * (P.tc.rat (diagGL δ) * g)) := by
      rw [hfactor]
      simp only [map_mul]
      group
    calc
      scalarOf P G Fs.f Fs.fC (P.tc.rat b * g) =
          scalarOf P G Fs.f Fs.fC
            (P.tc.rat (scalarGL c) * (P.tc.rat (upperGL x) *
              (P.tc.rat (diagGL δ) * g))) := by rw [harg]
      _ = scalarOf P G Fs.f Fs.fC
            (P.tc.rat (upperGL x) * (P.tc.rat (diagGL δ) * g)) := by
          rw [P.tc.rat_scalar, one_mul]
      _ = scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL δ) * g) :=
          scalarOf_upper_rat_invariance P G Fs x _
      _ = scalarOf P G Fs.f Fs.fC g := scalarOf_diag_invariance P G Fs δ hδ g
  · intro x g
    exact scalarOf_nS_invariance P G Fs x g
  · intro v hv x g
    exact scalarOf_n_invariance P G Fs v hv x g
  · intro ζ g
    obtain ⟨v⟩ := scalar_nonempty_finPlace (F := F)
    exact scalarOf_z_invariance_at P G Fs v ζ g

/-- **def:eisenstein**: `E(g, Φ) = Σ_{γ ∈ B_*(F)\GL₂(F)} Φ(γ g)`. -/
def eisenstein (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s)
    (g : P.tc.G) : ℂ :=
  ∑' γ : Quotient (QuotientGroup.rightRel (Bstar G)),
    scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out γ) * g)

open scoped nonZeroDivisors in
/-- Only finitely many rational torus classes have a nonzero finite-place scalar
product at a fixed restricted-product lift. -/
theorem finite_torus_scalar_support (P : CoverPackage D S H A)
    (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s) (r : P.RP) :
    Set.Finite {δ : Fˣ ⧸ G.Δ |
      (∏ᶠ v, G.lam v (Fs.f v
        ((P.loc v).a (toLoc v (Quotient.out δ)) * P.compF v r))) ≠ 0} := by
  classical
  let W : Finset (FinPlace F) := Fs.T0 ∪ (P.comp_restricted r).toFinset
  let cubes : Subgroup Fˣ := (powMonoidHom 3 : Fˣ →* Fˣ).range
  have hcubes : cubes ≤ (G.Δ).comap (MonoidHom.id Fˣ) := by
    rintro a ⟨b, rfl⟩
    change b ^ 3 ∈ G.Δ
    simp only [GlobalDatum.Δ, Subgroup.mem_iInf, Subgroup.mem_comap, map_pow]
    exact fun v => G.alag_cubes v (toLoc v b)
  let π : (Fˣ ⧸ cubes) →* (Fˣ ⧸ G.Δ) :=
    QuotientGroup.map cubes G.Δ (MonoidHom.id Fˣ) hcubes
  have hcomp (a : Fˣ) (v : FinPlace F) :
      P.compF v (P.ratRP (diagGL a) * r) =
        (P.loc v).a (toLoc v a) * P.compF v r := by
    have hdiag : Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (diagGL a) = diagM (v.adicCompletion F) (toLoc v a) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.map, diagGL, diagM, toLoc]
    rw [map_mul, P.compF_ratRP, hdiag, ← (P.loc v).sec_a]
  apply ((finite_cubic_valuation_classes F W).image π).subset
  intro δ hδ
  let a : Fˣ := Quotient.out δ
  change (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r))) ≠ 0 at hδ
  have hsupp : (Function.mulSupport fun v =>
      G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r))).Finite := by
    simpa only [hcomp] using (scalarOf_q P G Fs (P.ratRP (diagGL a) * r)).1
  have ha : ∀ v, v ∉ W → (3 : ℤ) ∣ FractionalIdeal.count F v
      (toPrincipalIdeal (𝓞 F) F a : FractionalIdeal (𝓞 F)⁰ F) := by
    intro v hv
    simp only [W, Finset.mem_union, not_or] at hv
    have hT0 : v ∉ Fs.T0 := hv.1
    have hSf : v ∉ S.Sf := fun h => hT0 (Fs.sub h)
    have hk : P.compF v r ∈ (P.tame v hSf).Kmax := by
      by_contra hk
      exact hv.2
        ((P.comp_restricted r).mem_toFinset.mpr ⟨hSf, hk⟩)
    by_contra hcount
    have hsec : Fs.f v ((P.loc v).a (toLoc v a)) =
        ((absFin v (toLoc v a) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          (G.T v).σa (toLoc v a) (Fs.f v 1) := by
      simpa only [ofAdd_zero, map_one, one_mul, mul_one]
        using (Fs.f_sec v).1 0 (toLoc v a) 1
    have hz : G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r)) = 0 := by
      rw [(Fs.f_sph v hT0).2 _ _ hk, hsec, (Fs.f_sph v hT0).1, map_smul]
      rw [tame_coefficient_eq_zero_of_count_not_dvd (G.T v) (G.B v hSf)
        (G.lam v) (G.lam_tame v hSf) a hcount, smul_zero]
    exact hδ (finprod_eq_zero _ v hz hsupp)
  refine ⟨(QuotientGroup.mk' cubes) a, ⟨a, ha, rfl⟩, ?_⟩
  change (QuotientGroup.mk' G.Δ) a = δ
  exact Quotient.out_eq δ

open scoped nonZeroDivisors in
/-- One finite torus support set works for every lift whose projected components
are tame compact outside a fixed finite set of places. -/
theorem finite_torus_scalar_support_uniform (P : CoverPackage D S H A)
    (G : GlobalDatum P) {s : ℂ} (Fs : GlobalSection P G s)
    (W : Finset (FinPlace F)) (hW : Fs.T0 ⊆ W) :
    ∃ U : Set (Fˣ ⧸ G.Δ), U.Finite ∧ ∀ r : P.RP,
      (∀ v (hv : v ∉ W),
        (P.loc v).pr (P.compF v r) ∈
          (P.loc v).pr ''
            ((P.tame v (fun h => hv (hW (Fs.sub h)))).Kmax : Set (P.loc v).L)) →
      {δ : Fˣ ⧸ G.Δ |
        (∏ᶠ v, G.lam v (Fs.f v
          ((P.loc v).a (toLoc v (Quotient.out δ)) * P.compF v r))) ≠ 0} ⊆ U := by
  classical
  let cubes : Subgroup Fˣ := (powMonoidHom 3 : Fˣ →* Fˣ).range
  have hcubes : cubes ≤ (G.Δ).comap (MonoidHom.id Fˣ) := by
    rintro a ⟨b, rfl⟩
    change b ^ 3 ∈ G.Δ
    simp only [GlobalDatum.Δ, Subgroup.mem_iInf, Subgroup.mem_comap, map_pow]
    exact fun v => G.alag_cubes v (toLoc v b)
  let π : (Fˣ ⧸ cubes) →* (Fˣ ⧸ G.Δ) :=
    QuotientGroup.map cubes G.Δ (MonoidHom.id Fˣ) hcubes
  let U : Set (Fˣ ⧸ G.Δ) := π ''
    ((QuotientGroup.mk' cubes) '' {a : Fˣ | ∀ v, v ∉ W →
      (3 : ℤ) ∣ FractionalIdeal.count F v
        (toPrincipalIdeal (𝓞 F) F a : FractionalIdeal (𝓞 F)⁰ F)})
  refine ⟨U, (finite_cubic_valuation_classes F W).image π, ?_⟩
  intro r hr δ hδ
  let a : Fˣ := Quotient.out δ
  change (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r))) ≠ 0 at hδ
  have hcomp (v : FinPlace F) :
      P.compF v (P.ratRP (diagGL a) * r) =
        (P.loc v).a (toLoc v a) * P.compF v r := by
    have hdiag : Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (diagGL a) = diagM (v.adicCompletion F) (toLoc v a) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.map, diagGL, diagM, toLoc]
    rw [map_mul, P.compF_ratRP, hdiag, ← (P.loc v).sec_a]
  have hsupp : (Function.mulSupport fun v =>
      G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r))).Finite := by
    simpa only [hcomp] using (scalarOf_q P G Fs (P.ratRP (diagGL a) * r)).1
  have ha : ∀ v, v ∉ W → (3 : ℤ) ∣ FractionalIdeal.count F v
      (toPrincipalIdeal (𝓞 F) F a : FractionalIdeal (𝓞 F)⁰ F) := by
    intro v hv
    have hT0 : v ∉ Fs.T0 := fun h => hv (hW h)
    have hSf : v ∉ S.Sf := fun h => hT0 (Fs.sub h)
    obtain ⟨k, hk, hkpr⟩ := hr v hv
    have hker : k⁻¹ * P.compF v r ∈ (P.loc v).pr.ker := by
      change (P.loc v).pr (k⁻¹ * P.compF v r) = 1
      rw [map_mul, map_inv, hkpr, inv_mul_cancel]
    rw [(P.loc v).pr_ker] at hker
    obtain ⟨ζ, hζ⟩ := hker
    have hrcomp : P.compF v r = (P.loc v).z ζ * k := by
      calc
        P.compF v r = k * (k⁻¹ * P.compF v r) := by group
        _ = k * (P.loc v).z ζ := by rw [← hζ]
        _ = (P.loc v).z ζ * k := ((P.loc v).z_central ζ k).symm
    by_contra hcount
    have hsec : Fs.f v ((P.loc v).a (toLoc v a)) =
        ((absFin v (toLoc v a) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          (G.T v).σa (toLoc v a) (Fs.f v 1) := by
      simpa only [ofAdd_zero, map_one, one_mul, mul_one]
        using (Fs.f_sec v).1 0 (toLoc v a) 1
    have hz : G.lam v (Fs.f v ((P.loc v).a (toLoc v a) * P.compF v r)) = 0 := by
      rw [hrcomp, ← mul_assoc,
        ← (P.loc v).z_central ζ ((P.loc v).a (toLoc v a)), mul_assoc,
        (Fs.f_sec v).2.1, map_smul, (Fs.f_sph v hT0).2 _ _ hk,
        hsec, (Fs.f_sph v hT0).1, map_smul,
        tame_coefficient_eq_zero_of_count_not_dvd (G.T v) (G.B v hSf)
          (G.lam v) (G.lam_tame v hSf) a hcount, smul_zero, smul_zero]
    exact hδ (finprod_eq_zero _ v hz hsupp)
  refine ⟨(QuotientGroup.mk' cubes) a, ⟨a, ha, rfl⟩, ?_⟩
  change (QuotientGroup.mk' G.Δ) a = δ
  exact Quotient.out_eq δ

/-- Rational Bstar representatives refine any surjective family of Borel cusp representatives. -/
theorem rational_cusp_factorization (P : CoverPackage D S H A)
    (G : GlobalDatum P)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
    {ι : Type} (σ : ι → Matrix.SpecialLinearGroup (Fin 2) F)
    (hσ : Function.Surjective
      (fun p : (Σ i, ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) =>
        Quotient.mk
          (QuotientGroup.rightRel (ArtinPrimitiveRoots.A1.Spec.borelSL F))
          ((σ p.1)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
            ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))))
    (g : GL (Fin 2) F) :
    ∃ (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i))
      (δ : Fˣ) (b : GL (Fin 2) F), b ∈ Bstar G ∧
      g = b * diagGL δ * Matrix.SpecialLinearGroup.toGL
        ((σ i)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
          ((q.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) := by
  classical
  have hdiag (δ : Fˣ) : Matrix.GeneralLinearGroup.det (diagGL δ) = δ := by
    apply Units.ext
    change (diagGL δ : Matrix (Fin 2) (Fin 2) F).det = (δ : F)
    simp [diagGL, Matrix.det_fin_two]
  let d : Fˣ := Matrix.GeneralLinearGroup.det g
  have hk : (diagGL d)⁻¹ * g ∈ Matrix.GeneralLinearGroup.det.ker := by
    change Matrix.GeneralLinearGroup.det ((diagGL d)⁻¹ * g) = 1
    rw [map_mul, map_inv, hdiag]
    exact inv_mul_cancel d
  rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hk
  obtain ⟨γ, hγ⟩ := hk
  obtain ⟨⟨i, q⟩, hq⟩ := hσ (Quotient.mk _ γ)
  let c : Matrix.SpecialLinearGroup (Fin 2) F :=
    (σ i)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
      ((q.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
  change Quotient.mk (QuotientGroup.rightRel (ArtinPrimitiveRoots.A1.Spec.borelSL F)) c =
    Quotient.mk (QuotientGroup.rightRel (ArtinPrimitiveRoots.A1.Spec.borelSL F)) γ at hq
  let u : Matrix.SpecialLinearGroup (Fin 2) F := γ * c⁻¹
  have hu : u 1 0 = 0 :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
  let a : GL (Fin 2) F := diagGL d * Matrix.SpecialLinearGroup.toGL u
  have hga : g = a * Matrix.SpecialLinearGroup.toGL c := by
    calc
      g = diagGL d * Matrix.SpecialLinearGroup.toGL γ := by rw [hγ]; group
      _ = (diagGL d * Matrix.SpecialLinearGroup.toGL (γ * c⁻¹)) *
          Matrix.SpecialLinearGroup.toGL c := by rw [map_mul, map_inv]; group
      _ = _ := rfl
  let M : Matrix (Fin 2) (Fin 2) F := a
  have h10 : M 1 0 = 0 := by
    change ((diagGL d : Matrix (Fin 2) (Fin 2) F) *
      (u : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0
    simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two, hu]
  have hdet : M 0 0 * M 1 1 ≠ 0 := by
    have hd := Matrix.GeneralLinearGroup.det_ne_zero a
    change M.det ≠ 0 at hd
    simpa only [Matrix.det_fin_two, h10, mul_zero, sub_zero] using hd
  have h00 : M 0 0 ≠ 0 := (mul_ne_zero_iff.mp hdet).1
  have h11 : M 1 1 ≠ 0 := (mul_ne_zero_iff.mp hdet).2
  let δ : Fˣ := Units.mk0 (M 0 0 / M 1 1) (div_ne_zero h00 h11)
  let b : GL (Fin 2) F :=
    scalarGL (Units.mk0 (M 1 1) h11) * upperGL (M 0 1 / M 1 1)
  have hb : b ∈ Bstar G := by
    refine ⟨?_, 1, G.Δ.one_mem, ?_⟩
    · simp [b, scalarGL, upperGL, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [b, scalarGL, upperGL, Matrix.mul_apply, Fin.sum_univ_two]
  have ha : a = b * diagGL δ := by
    apply Units.ext
    change M = (b : Matrix (Fin 2) (Fin 2) F) * (diagGL δ : Matrix (Fin 2) (Fin 2) F)
    ext j k
    fin_cases j <;> fin_cases k
    all_goals simp [b, δ, scalarGL, upperGL, diagGL, Matrix.mul_apply,
      Fin.sum_univ_two, h10]
    all_goals field_simp
  refine ⟨i, q, δ, b, hb, ?_⟩
  exact hga.trans (congrArg (fun t => t * Matrix.SpecialLinearGroup.toGL c) ha)

/-- The finite torus support remains uniform over integral translates of a finite rational family. -/
theorem finite_integral_translate_torus_support
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) {ι : Type} [Fintype ι]
    (c : ι → GL (Fin 2) F) (r : P.RP) :
    ∃ U : Set (Fˣ ⧸ G.Δ), U.Finite ∧
      ∀ (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)),
        {δ : Fˣ ⧸ G.Δ |
          (∏ᶠ v, G.lam v (Fs.f v
            ((P.loc v).a (toLoc v (Quotient.out δ)) *
              P.compF v (P.ratRP
                (c i * Matrix.SpecialLinearGroup.toGL
                  (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * r)))) ≠ 0} ⊆ U := by
  classical
  let W : Finset (FinPlace F) := Fs.T0 ∪ (P.comp_restricted r).toFinset ∪
    Finset.univ.biUnion (fun i : ι => (P.comp_restricted (P.ratRP (c i))).toFinset)
  have hW : Fs.T0 ⊆ W := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
  have hIntegral (v : FinPlace F) (hSf : v ∉ S.Sf)
      (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      (P.loc v).pr (P.compF v (P.ratRP (Matrix.SpecialLinearGroup.toGL
        (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)))) ∈
        (P.loc v).pr '' ((P.tame v hSf).Kmax : Set (P.loc v).L) := by
    rw [P.compF_ratRP, (P.loc v).sec_pr, (P.tame v hSf).image]
    let k : GL (Fin 2) (v.adicCompletion F) :=
      Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toSLF F γ))
    refine ⟨k, ?_, ?_, rfl⟩
    · intro j l
      change ((algebraMap (𝓞 F) F (γ j l) : F) : v.adicCompletion F) ∈
        v.adicCompletionIntegers F
      exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v (γ j l)
    · have hdet : Matrix.GeneralLinearGroup.det k = 1 := by
        simp [k, Matrix.GeneralLinearGroup.map_det]
      have hdetinv : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det = 1 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv, hdet]
        rfl
      rw [hdetinv]
      exact (v.adicCompletionIntegers F).one_mem
  have hproj (v : FinPlace F) (a b : GL (Fin 2) F) :
      (P.loc v).pr (P.compF v (P.ratRP (a * b))) =
        (P.loc v).pr (P.compF v (P.ratRP a)) *
          (P.loc v).pr (P.compF v (P.ratRP b)) := by
    simp only [P.compF_ratRP, (P.loc v).sec_pr, map_mul, QuotientGroup.mk_mul]
  obtain ⟨U, hU, hcover⟩ := finite_torus_scalar_support_uniform P G Fs W hW
  refine ⟨U, hU, ?_⟩
  intro i γ
  apply hcover
  intro v hv
  have hSf : v ∉ S.Sf := fun h => hv (hW (Fs.sub h))
  have hVr : v ∉ (P.comp_restricted r).toFinset := by
    intro h
    exact hv (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
  have hVc : v ∉ (P.comp_restricted (P.ratRP (c i))).toFinset := by
    intro h
    exact hv (Finset.mem_union.mpr (Or.inr
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)))
  have hkr : P.compF v r ∈ (P.tame v hSf).Kmax := by
    by_contra h
    exact hVr ((P.comp_restricted r).mem_toFinset.mpr ⟨hSf, h⟩)
  have hkc : P.compF v (P.ratRP (c i)) ∈ (P.tame v hSf).Kmax := by
    by_contra h
    exact hVc ((P.comp_restricted (P.ratRP (c i))).mem_toFinset.mpr ⟨hSf, h⟩)
  obtain ⟨k, hk, hkpr⟩ := hIntegral v hSf γ
  refine ⟨P.compF v (P.ratRP (c i)) * k * P.compF v r,
    (P.tame v hSf).Kmax.mul_mem ((P.tame v hSf).Kmax.mul_mem hkc hk) hkr, ?_⟩
  simp only [map_mul, hkpr, hproj]

/-- Finite-place scalar products are uniformly bounded on integral translates of a finite rational family. -/
theorem finite_scalar_integral_translate_bound
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) {ι : Type} [Fintype ι]
    (c : ι → GL (Fin 2) F) (r : P.RP) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)),
        ‖∏ᶠ v, G.lam v (Fs.f v (P.compF v
          (P.ratRP (c i * Matrix.SpecialLinearGroup.toGL
            (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * r)))‖ ≤ C := by
  classical
  let j : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) →* GL (Fin 2) F :=
    Matrix.SpecialLinearGroup.toGL.comp (ArtinPrimitiveRoots.A1.Spec.toSLF F)
  let jv (v : FinPlace F) :
      Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) →* GL (Fin 2) (v.adicCompletion F) :=
    (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))).comp j
  let Kint (v : FinPlace F) : Set (GL (Fin 2) (v.adicCompletion F)) :=
    {k | (∀ a b, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) a b ∈
      v.adicCompletionIntegers F) ∧ ∀ a b,
        ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F}
  let R (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) : P.RP :=
    P.ratRP (c i * j γ) * r
  let bcoeff (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) (v : FinPlace F) : ℂ :=
    G.lam v (Fs.f v (P.compF v (R i γ)))
  have hentries (v : FinPlace F) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (a b : Fin 2) : (jv v γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) a b ∈
        v.adicCompletionIntegers F := by
    change ((algebraMap (𝓞 F) F (γ a b) : F) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F
    exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v (γ a b)
  have hKint (v : FinPlace F) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      jv v γ ∈ Kint v := by
    refine ⟨hentries v γ, ?_⟩
    intro a b
    rw [← map_inv]
    exact hentries v γ⁻¹ a b
  have hlocal (i : ι) (v : FinPlace F) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F), ‖bcoeff i γ v‖ ≤ C := by
    let φ : GL (Fin 2) (v.adicCompletion F) → PGL2 (v.adicCompletion F) :=
      fun k => QuotientGroup.mk
        (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (c i) * k) *
          (P.loc v).pr (P.compF v r)
    have hφ : Continuous φ := by
      dsimp only [φ]
      have hleft : Continuous (fun k : GL (Fin 2) (v.adicCompletion F) =>
          Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (c i) * k) :=
        continuous_const.mul continuous_id
      have hquot : Continuous (fun k : GL (Fin 2) (v.adicCompletion F) =>
          (QuotientGroup.mk
            (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (c i) * k) :
              PGL2 (v.adicCompletion F))) := QuotientGroup.continuous_mk.comp hleft
      exact hquot.mul continuous_const
    let K : Set (P.loc v).L := (P.loc v).pr ⁻¹' (φ '' Kint v)
    have hK : IsCompact K := local_cover_compact_preimage (P.loc v) _
      ((local_integral_units_compact v).image hφ)
    obtain ⟨B, hB, hbound⟩ := section_norm_bound_on_compact
      (P.loc v) (G.T v) (Fs.f v) (Fs.f_sec v) K hK
    let lam : (G.T v).V →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (G.lam v)
    refine ⟨‖lam‖ * B, mul_nonneg (norm_nonneg _) hB, ?_⟩
    intro γ
    have hmem : P.compF v (R i γ) ∈ K := by
      refine ⟨jv v γ, hKint v γ, ?_⟩
      simp only [φ, R, jv, MonoidHom.comp_apply, map_mul, P.compF_ratRP,
        (P.loc v).sec_pr, QuotientGroup.mk_mul]
    exact (lam.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hbound _ hmem) (norm_nonneg lam))
  choose Cv hCv hCvbound using hlocal
  let W : Finset (FinPlace F) := Fs.T0 ∪ (P.comp_restricted r).toFinset ∪
    Finset.univ.biUnion (fun i : ι => (P.comp_restricted (P.ratRP (c i))).toFinset)
  have hW : Fs.T0 ⊆ W := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
  let pj (v : FinPlace F) (a : GL (Fin 2) F) : PGL2 (v.adicCompletion F) :=
    (P.loc v).pr (P.compF v (P.ratRP a))
  have hpj (v : FinPlace F) (a b : GL (Fin 2) F) :
      pj v (a * b) = pj v a * pj v b := by
    simp only [pj, P.compF_ratRP, (P.loc v).sec_pr, map_mul, QuotientGroup.mk_mul]
  have hIntegral (v : FinPlace F) (hSf : v ∉ S.Sf)
      (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      pj v (j γ) ∈ (P.loc v).pr '' ((P.tame v hSf).Kmax : Set (P.loc v).L) := by
    dsimp only [pj]
    rw [P.compF_ratRP, (P.loc v).sec_pr, (P.tame v hSf).image]
    refine ⟨jv v γ, hentries v γ, ?_, rfl⟩
    have hdet : Matrix.GeneralLinearGroup.det (jv v γ) = 1 := by
      simp [jv, j, Matrix.GeneralLinearGroup.map_det]
    have hdetinv : (jv v γ)⁻¹.val.det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv, hdet]
      rfl
    rw [hdetinv]
    exact (v.adicCompletionIntegers F).one_mem
  have hprojTame (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (v : FinPlace F) (hv : v ∉ W) :
      (P.loc v).pr (P.compF v (R i γ)) ∈ (P.loc v).pr ''
        ((P.tame v (fun h => hv (hW (Fs.sub h)))).Kmax : Set (P.loc v).L) := by
    have hSf : v ∉ S.Sf := fun h => hv (hW (Fs.sub h))
    have hVr : v ∉ (P.comp_restricted r).toFinset := by
      intro h
      exact hv (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
    have hVc : v ∉ (P.comp_restricted (P.ratRP (c i))).toFinset := by
      intro h
      exact hv (Finset.mem_union.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)))
    have hkr : P.compF v r ∈ (P.tame v hSf).Kmax := by
      by_contra h
      exact hVr ((P.comp_restricted r).mem_toFinset.mpr ⟨hSf, h⟩)
    have hkc : P.compF v (P.ratRP (c i)) ∈ (P.tame v hSf).Kmax := by
      by_contra h
      exact hVc ((P.comp_restricted (P.ratRP (c i))).mem_toFinset.mpr ⟨hSf, h⟩)
    obtain ⟨k, hk, hkpr⟩ := hIntegral v hSf γ
    refine ⟨P.compF v (P.ratRP (c i)) * k * P.compF v r,
      (P.tame v hSf).Kmax.mul_mem ((P.tame v hSf).Kmax.mul_mem hkc hk) hkr, ?_⟩
    simp only [R, map_mul]
    change (pj v (c i) * (P.loc v).pr k) * (P.loc v).pr (P.compF v r) =
      pj v (c i * j γ) * (P.loc v).pr (P.compF v r)
    rw [hkpr, hpj]
  have hunitnorm (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (v : FinPlace F) (hv : v ∉ W) : ‖bcoeff i γ v‖ = 1 := by
    have hT0 : v ∉ Fs.T0 := fun h => hv (hW h)
    have hSf : v ∉ S.Sf := fun h => hT0 (Fs.sub h)
    obtain ⟨k, hk, hkpr⟩ := hprojTame i γ v hv
    have hker : P.compF v (R i γ) * k⁻¹ ∈ (P.loc v).pr.ker := by
      change (P.loc v).pr (P.compF v (R i γ) * k⁻¹) = 1
      rw [map_mul, map_inv, ← hkpr, mul_inv_cancel]
    rw [(P.loc v).pr_ker] at hker
    obtain ⟨ζ, hζ⟩ := hker
    have hcomp : P.compF v (R i γ) = (P.loc v).z ζ * k := by
      rw [hζ]
      simp only [inv_mul_cancel_right]
    have hfk : Fs.f v k = Fs.f v 1 := by
      simpa only [one_mul] using (Fs.f_sph v hT0).2 1 k hk
    have hcoeff : bcoeff i γ v = ((ζ : ℂˣ) : ℂ) := by
      dsimp only [bcoeff]
      rw [hcomp, (Fs.f_sec v).2.1, map_smul, hfk, (Fs.f_sph v hT0).1,
        G.lam_tame v hSf 0]
      simp
    have hζpow : (((ζ : ℂˣ) : ℂ)) ^ 3 = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun u : ℂˣ => (u : ℂ)) ((mem_rootsOfUnity 3 (ζ : ℂˣ)).mp ζ.property)
    rw [hcoeff]
    exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hζpow⟩).norm_eq_one
  let Ci (i : ι) : ℝ := ∏ v ∈ W, Cv i v
  have hCi (i : ι) : 0 ≤ Ci i := Finset.prod_nonneg fun v _ => hCv i v
  refine ⟨∑ i, Ci i, Finset.sum_nonneg (fun i _ => hCi i), ?_⟩
  intro i γ
  change ‖∏ᶠ v, bcoeff i γ v‖ ≤ ∑ a, Ci a
  have hsupp : (Function.mulSupport (bcoeff i γ)).Finite :=
    (scalarOf_q P G Fs (R i γ)).1
  have heqnorm : ‖∏ᶠ v, bcoeff i γ v‖ = ∏ v ∈ W, ‖bcoeff i γ v‖ := by
    change (normHom.toMonoidHom : ℂ →* ℝ) (∏ᶠ v, bcoeff i γ v) = _
    rw [(normHom.toMonoidHom : ℂ →* ℝ).map_finprod hsupp]
    change (∏ᶠ v, ‖bcoeff i γ v‖) = _
    exact finprod_eq_prod_of_mulSupport_subset _
      (Function.mulSupport_subset_iff'.mpr fun v hv => hunitnorm i γ v hv)
  rw [heqnorm]
  exact (Finset.prod_le_prod₀ (fun v _ => norm_nonneg (bcoeff i γ v))
    (fun v _ => hCvbound i v γ)).trans
      (Finset.single_le_sum (fun a _ => hCi a) (Finset.mem_univ i))

/-- Uniform scalar height bounds over integral translates of a finite cusp and torus family. -/
theorem scalar_cusp_height_majorant
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) {ι : Type} [Fintype ι]
    (c : ι → Matrix.SpecialLinearGroup (Fin 2) F)
    (δ : ι → Fˣ) (r : P.RP) :
    ∃ z : ArtinPrimitiveRoots.A1.Spec.X F, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)),
        ‖scalarOf P G Fs.f Fs.fC
          (P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL
            (c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * P.q r)‖ ≤
          C * ArtinPrimitiveRoots.A1.Spec.normHeight F
            ((c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • z) ^ (1 + 2 * s.re) := by
  classical
  choose Cw hCw hbound using fun w =>
    sectionC_norm_majorant s (Fs.fC w) (Fs.fC_sec w).1 (Fs.fC_sec w).2
  obtain ⟨z, hz⟩ := complex_spherical_height_product (fun w => P.compC w r)
  obtain ⟨Cf, hCf, hfbound⟩ := finite_scalar_integral_translate_bound P G Fs
    (fun i => diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (c i)) r
  let t (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :=
    c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ
  let R (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) : P.RP :=
    P.ratRP (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) * r
  let y (i : ι) (w : InfinitePlace F) : ℂˣ := Units.map w.embedding.toMonoidHom (δ i)
  let U (w : InfinitePlace F) (a : Matrix.SpecialLinearGroup (Fin 2) F) : PGL2 ℂ :=
    QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL
      (ArtinPrimitiveRoots.A1.Spec.toInf F a w)) * P.compC w r
  let A (i : ι) (w : InfinitePlace F) : ℝ :=
    ‖(Complex.normSq (y i w : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)‖ * Cw w
  let Ai (i : ι) : ℝ := ∏ w, A i w
  have hA (i : ι) (w : InfinitePlace F) : 0 ≤ A i w :=
    mul_nonneg (norm_nonneg _) (hCw w)
  have hAi (i : ι) : 0 ≤ Ai i := Finset.prod_nonneg fun w _ => hA i w
  have hdiag (i : ι) (w : InfinitePlace F) :
      Matrix.GeneralLinearGroup.map w.embedding (diagGL (δ i)) = diagM ℂ (y i w) := by
    apply Units.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.GeneralLinearGroup.map, diagGL, diagM, y]
  have hsl (w : InfinitePlace F) (a : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix.GeneralLinearGroup.map w.embedding (Matrix.SpecialLinearGroup.toGL a) =
        Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toInf F a w) := by
    apply Units.ext
    rfl
  have hcomp (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) (w : InfinitePlace F) :
      P.compC w (R i γ) = QuotientGroup.mk (diagM ℂ (y i w)) * U w (t i γ) := by
    dsimp only [R]
    rw [map_mul, P.compC_ratRP, map_mul, hdiag, hsl, QuotientGroup.mk_mul]
    exact mul_assoc _ _ _
  have hzero : upperM ℂ 0 = 1 := by
    apply Units.ext
    ext a b
    fin_cases a <;> fin_cases b <;> simp [upperM]
  have hsec (w : InfinitePlace F) (a : ℂˣ) (k : PGL2 ℂ) :
      Fs.fC w (QuotientGroup.mk (diagM ℂ a) * k) =
        (Complex.normSq (a : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s) * Fs.fC w k := by
    simpa only [hzero, QuotientGroup.mk_one, one_mul] using (Fs.fC_sec w).1 0 a k
  have hlocal (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) (w : InfinitePlace F) :
      ‖Fs.fC w (P.compC w (R i γ))‖ ≤ A i w * ‖sphC (s.re : ℂ) (U w (t i γ))‖ := by
    rw [hcomp, hsec, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbound w (U w (t i γ))) (norm_nonneg _)).trans_eq
      (by dsimp [A]; ring)
  have hheight (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      (∏ w, ‖sphC (s.re : ℂ) (U w (t i γ))‖) =
        ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • z) ^ (1 + 2 * s.re) :=
    hz s.re (t i γ)
  have hheight_nonneg (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      0 ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • z) ^ (1 + 2 * s.re) := by
    rw [← hheight]
    exact Finset.prod_nonneg fun w _ => norm_nonneg _
  have hinf (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :
      (∏ w, ‖Fs.fC w (P.compC w (R i γ))‖) ≤
        Ai i * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • z) ^ (1 + 2 * s.re) := by
    calc
      _ ≤ ∏ w, A i w * ‖sphC (s.re : ℂ) (U w (t i γ))‖ :=
        Finset.prod_le_prod₀ (fun w _ => norm_nonneg _) (fun w _ => hlocal i γ w)
      _ = _ := by rw [Finset.prod_mul_distrib, hheight]
  refine ⟨z, Cf * ∑ i, Ai i, mul_nonneg hCf (Finset.sum_nonneg fun i _ => hAi i), ?_⟩
  intro i γ
  have hq : P.q (R i γ) =
      P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) * P.q r := by
    simp only [R, map_mul, P.q_ratRP]
  change ‖scalarOf P G Fs.f Fs.fC
    (P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) * P.q r)‖ ≤ _
  rw [← hq, (scalarOf_q P G Fs (R i γ)).2, norm_mul, norm_prod]
  have hf : ‖∏ᶠ v, G.lam v (Fs.f v (P.compF v (R i γ)))‖ ≤ Cf := by
    simpa only [R, t, map_mul, mul_assoc] using hfbound i γ
  calc
    _ ≤ Cf * (Ai i * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • z) ^
        (1 + 2 * s.re)) :=
      mul_le_mul hf (hinf i γ) (Finset.prod_nonneg fun w _ => norm_nonneg _) hCf
    _ = (Cf * Ai i) * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • z) ^
        (1 + 2 * s.re) := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun a _ => hAi a) (Finset.mem_univ i)) hCf)
      (hheight_nonneg i γ)

/-- Every nonzero scalar summand has a cusp representative in one finite torus family. -/
theorem finite_supported_cusp_representatives
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
    {ι : Type} [Fintype ι] (σ : ι → Matrix.SpecialLinearGroup (Fin 2) F)
    (hσ : Function.Surjective
      (fun p : (Σ i, ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) =>
        Quotient.mk
          (QuotientGroup.rightRel (ArtinPrimitiveRoots.A1.Spec.borelSL F))
          ((σ p.1)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
            ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))))
    (r : P.RP) :
    ∃ U : Set (Fˣ ⧸ G.Δ), U.Finite ∧
      ∀ β : Quotient (QuotientGroup.rightRel (Bstar G)),
        scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * P.q r) ≠ 0 →
        ∃ (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i))
          (δ : Fˣ ⧸ G.Δ), δ ∈ U ∧
            β = Quotient.mk (QuotientGroup.rightRel (Bstar G))
              (diagGL (Quotient.out δ) * Matrix.SpecialLinearGroup.toGL
                ((σ i)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
                  ((q.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))) := by
  classical
  obtain ⟨U, hU, hsupport⟩ := finite_integral_translate_torus_support P G Fs
    (fun i => Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹)) r
  have hdiag_mul (a d : Fˣ) : diagGL (a * d) = diagGL a * diagGL d := by
    apply Units.ext
    ext j l
    fin_cases j <;> fin_cases l <;>
      simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two]
  have hdiag_mem (a : Fˣ) (ha : a ∈ G.Δ) : diagGL a ∈ Bstar G := by
    change (diagGL a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ d ∈ G.Δ, (diagGL a : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (d : F) * (diagGL a : Matrix (Fin 2) (Fin 2) F) 1 1
    exact ⟨by simp [diagGL], a, ha, by simp [diagGL]⟩
  have hcomp (a : Fˣ) (x : P.RP) (v : FinPlace F) :
      P.compF v (P.ratRP (diagGL a) * x) =
        (P.loc v).a (toLoc v a) * P.compF v x := by
    have hdiag : Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (diagGL a) = diagM (v.adicCompletion F) (toLoc v a) := by
      apply Units.ext
      ext j l
      fin_cases j <;> fin_cases l <;>
        simp [Matrix.GeneralLinearGroup.map, diagGL, diagM, toLoc]
    rw [map_mul, P.compF_ratRP, hdiag, ← (P.loc v).sec_a]
  refine ⟨U, hU, ?_⟩
  intro β hβ
  obtain ⟨i, q, a, b, hb, hfactor⟩ :=
    rational_cusp_factorization P G Γ σ hσ (Quotient.out β)
  let γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) := (q.out : Γ)
  let k : GL (Fin 2) F := Matrix.SpecialLinearGroup.toGL
    ((σ i)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F γ)
  let δ : Fˣ ⧸ G.Δ := QuotientGroup.mk a
  let d : Fˣ := Quotient.out δ
  let e : Fˣ := a * d⁻¹
  have he : e ∈ G.Δ := by
    have heq : (QuotientGroup.mk a : Fˣ ⧸ G.Δ) = QuotientGroup.mk d :=
      (QuotientGroup.out_eq' δ).symm
    simpa only [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem.mp heq)
  let b' : GL (Fin 2) F := b * diagGL e
  have hb' : b' ∈ Bstar G := (Bstar G).mul_mem hb (hdiag_mem e he)
  have had : a = e * d := by dsimp only [e]; group
  have hfactor' : Quotient.out β = b' * (diagGL d * k) := by
    change Quotient.out β = b * diagGL a * k at hfactor
    rw [hfactor, had, hdiag_mul]
    dsimp only [b']
    group
  have hscalar :
      scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * P.q r) =
        scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL d * k) * P.q r) := by
    rw [hfactor', map_mul, mul_assoc]
    exact (scalarOf_invariance P G Fs).1 b' hb' _
  let x : P.RP := P.ratRP k * r
  let y : P.RP := P.ratRP (diagGL d) * x
  have hq : P.q y = P.tc.rat (diagGL d * k) * P.q r := by
    simp only [y, x, map_mul, P.q_ratRP, mul_assoc]
  have hnonzero : scalarOf P G Fs.f Fs.fC (P.q y) ≠ 0 := by
    rw [hq]
    exact fun h => hβ (hscalar.trans h)
  rw [(scalarOf_q P G Fs y).2] at hnonzero
  have hfinite :
      (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v d) * P.compF v x))) ≠ 0 := by
    simpa only [y, hcomp] using (mul_ne_zero_iff.mp hnonzero).1
  have hk : k = Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹) *
      Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toSLF F γ) := by
    dsimp only [k]
    rw [map_mul]
  have hδ : δ ∈ U := by
    apply hsupport i γ
    change (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v d) *
      P.compF v (P.ratRP (Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹) *
        Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * r)))) ≠ 0
    simpa only [x, hk] using hfinite
  refine ⟨i, q, δ, hδ, ?_⟩
  change β = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (diagGL d * k)
  calc
    β = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (Quotient.out β) :=
      (Quotient.out_eq β).symm
    _ = _ := by
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      rw [hfactor']
      simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using (Bstar G).inv_mem hb'

/-- Finite cusp majorants after bounding the complex components by real spherical sections. -/
theorem eisenstein_finite_majorants (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (C : InfinitePlace F → ℝ) (hC : ∀ w, 0 ≤ C w)
    (hbound : ∀ w k, ‖Fs.fC w k‖ ≤ C w * ‖sphC (s.re : ℂ) k‖) :
    ∃ (n : ℕ) (m : Fin n → Quotient (QuotientGroup.rightRel (Bstar G)) → ℝ),
      (∀ i, Summable (m i)) ∧ ∀ γ,
        ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out γ) * g)‖ ≤ ∑ i, m i γ := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) := ⊤
  letI : Γ.FiniteIndex := by dsimp only [Γ]; infer_instance
  obtain ⟨ι, hι, σ, hσ⟩ := ArtinPrimitiveRoots.A1.Spec.exists_cusp_reps F Γ
  letI : Fintype ι := hι
  obtain ⟨r, rfl⟩ := P.q_surj g
  obtain ⟨U, hU, hcover⟩ := finite_supported_cusp_representatives P G Fs Γ σ hσ.2 r
  letI : Fintype U := hU.fintype
  let J := U × ι
  obtain ⟨z, C0, hC0, hscalar⟩ := scalar_cusp_height_majorant P G Fs
    (fun j : J => (σ j.2)⁻¹) (fun j : J => Quotient.out j.1.1) r
  choose m hm hmbound using fun i =>
    ArtinPrimitiveRoots.A1.Spec.eisSeries_majorant F Γ (σ i)
      ({z} : Set (ArtinPrimitiveRoots.A1.Spec.X F)) isCompact_singleton s.re s.re hs
  have hm_bound (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) :
      ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ i) (s.re : ℂ) z q‖ ≤ m i q := by
    exact hmbound i z (Set.mem_singleton z) (s.re : ℂ) (by simp) (by simp) q
  have hm_nonneg (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) :
      0 ≤ m i q := (norm_nonneg _).trans (hm_bound i q)
  let Ξ := Σ j : J, ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ j.2)
  let M : Ξ → ℝ := fun p => C0 * m p.1.2 p.2
  have hM_nonneg (p : Ξ) : 0 ≤ M p := mul_nonneg hC0 (hm_nonneg p.1.2 p.2)
  have hM : Summable M := by
    apply (summable_sigma_of_nonneg hM_nonneg).2
    constructor
    · intro j
      exact (hm j.2).mul_left C0
    · exact (hasSum_fintype _).summable
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  let f : Q → ℝ := fun β =>
    ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * P.q r)‖
  let V : Set Q := Function.support f
  let a (p : Ξ) : GL (Fin 2) F :=
    diagGL (Quotient.out p.1.1.1) * Matrix.SpecialLinearGroup.toGL
      ((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
        ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
  let ret : Ξ → Q := fun p => Quotient.mk (QuotientGroup.rightRel (Bstar G)) (a p)
  have hparam : ∀ β : V, ∃ p : Ξ, ret p = β.1 := by
    intro β
    have hn : scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β.1) * P.q r) ≠ 0 :=
      norm_ne_zero_iff.mp β.property
    obtain ⟨i, q, δ, hδ, heq⟩ := hcover β.1 hn
    exact ⟨⟨(⟨δ, hδ⟩, i), q⟩, heq.symm⟩
  choose φ hφ using hparam
  have hφinj : Function.Injective φ := by
    intro β η heq
    apply Subtype.ext
    calc
      β.1 = ret (φ β) := (hφ β).symm
      _ = ret (φ η) := congrArg ret heq
      _ = η.1 := hφ η
  have hrep (b d : GL (Fin 2) F) (hbd : QuotientGroup.rightRel (Bstar G) b d) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat b * P.q r) =
        scalarOf P G Fs.f Fs.fC (P.tc.rat d * P.q r) := by
    have hd : d * b⁻¹ ∈ Bstar G := QuotientGroup.rightRel_apply.mp hbd
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (d * b⁻¹) hd (P.tc.rat b * P.q r)).symm
  have hterm (p : Ξ) :
      ArtinPrimitiveRoots.A1.Spec.normHeight F
        (((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
          ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) • z) ^
          (1 + 2 * s.re) =
        ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ p.1.2) (s.re : ℂ) z p.2‖ := by
    let γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) := (p.2.out : Γ)
    let y := ((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • z
    have hpos : 0 < ArtinPrimitiveRoots.A1.Spec.normHeight F y := by
      apply Finset.prod_pos
      intro w _
      rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (y w)
    have hact : (σ p.1.2)⁻¹ • (γ • z) = y := by
      change (σ p.1.2)⁻¹ • ((ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • z) = y
      exact (mul_smul _ _ _).symm
    change ArtinPrimitiveRoots.A1.Spec.normHeight F y ^ (1 + 2 * s.re) = _
    unfold ArtinPrimitiveRoots.A1.Spec.eisTerm
    change _ = ‖(ArtinPrimitiveRoots.A1.Spec.normHeight F
      ((σ p.1.2)⁻¹ • (γ • z)) : ℂ) ^ (1 + 2 * (s.re : ℂ))‖
    rw [hact, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hbound_support (β : V) : f β.1 ≤ M (φ β) := by
    have hcoset : QuotientGroup.rightRel (Bstar G) (Quotient.out β.1) (a (φ β)) := by
      apply Quotient.exact
      exact (Quotient.out_eq β.1).trans (hφ β).symm
    calc
      f β.1 = ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (a (φ β)) * P.q r)‖ :=
        congrArg norm (hrep _ _ hcoset)
      _ ≤ C0 * ArtinPrimitiveRoots.A1.Spec.normHeight F
          (((σ (φ β).1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
            (((φ β).2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) • z) ^
            (1 + 2 * s.re) :=
        hscalar (φ β).1 (((φ β).2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      _ = C0 * ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ (φ β).1.2)
          (s.re : ℂ) z (φ β).2‖ := congrArg (C0 * ·) (hterm (φ β))
      _ ≤ M (φ β) := mul_le_mul_of_nonneg_left (hm_bound _ _) hC0
  have hsupp : Summable (fun β : V => f β.1) :=
    Summable.of_nonneg_of_le (fun β => norm_nonneg _) hbound_support (hM.comp_injective hφinj)
  have hf : Summable f :=
    ((hasSum_subtype_iff_of_support_subset (s := V) (Set.Subset.refl _)).1 hsupp.hasSum).summable
  refine ⟨1, fun _ => f, fun _ => hf, ?_⟩
  intro β
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
  exact le_rfl

/-- **eis:converge** (via P-REDUCTION and P-SPEC `eisSeries_majorant`): absolute convergence for
`Re s > 1/2`. C6 of `sol-gate-theta` strengthens the input datum to exclude divergent cube repeats. -/
theorem eisenstein_summable (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G) :
    Summable fun γ : Quotient (QuotientGroup.rightRel (Bstar G)) =>
      ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out γ) * g)‖ := by
  classical
  choose C hC hbound using fun w =>
    sectionC_norm_majorant s (Fs.fC w) (Fs.fC_sec w).1 (Fs.fC_sec w).2
  obtain ⟨n, m, hm, hmajorant⟩ := eisenstein_finite_majorants P G hs Fs g C hC hbound
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmajorant
  exact summable_sum fun i _ => hm i

/-- **eis:automorphic**: in the convergence region `E` is automorphic, genuine, and right-invariant
under every element fixing all local sections. -/
theorem eisenstein_automorphic (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) :
    (∀ γ g, eisenstein P G Fs (P.tc.rat γ * g) = eisenstein P G Fs g) ∧
    (∀ ζ g, eisenstein P G Fs (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * eisenstein P G Fs g) ∧
    (∀ k : P.tc.G, (∀ h, scalarOf P G Fs.f Fs.fC (h * k) = scalarOf P G Fs.f Fs.fC h) →
      ∀ g, eisenstein P G Fs (g * k) = eisenstein P G Fs g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ g
    exact leftCosetSum_rightTranslate (Bstar G) P.tc.rat
      (scalarOf P G Fs.f Fs.fC) (scalarOf_invariance P G Fs).1 γ g
  · intro ζ g
    unfold eisenstein
    calc
      _ = ∑' q : Quotient (QuotientGroup.rightRel (Bstar G)),
          ((ζ : ℂˣ) : ℂ) * scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out q) * g) := by
        apply tsum_congr
        intro q
        rw [← mul_assoc, ← P.tc.z_central ζ, mul_assoc]
        exact (scalarOf_invariance P G Fs).2.2.2 ζ _
      _ = _ := tsum_mul_left
  · intro k hk g
    unfold eisenstein
    apply tsum_congr
    intro q
    simpa only [← mul_assoc] using hk (P.tc.rat (Quotient.out q) * g)

/-- The infinite embedding `F → ℂ^{places}`. -/
def infEmbA : F →+* (InfinitePlace F → ℂ) := RingHom.pi fun w => w.embedding

/-- `n(x)` at the archimedean places. -/
def nInf (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) : P.tc.G :=
  P.tc.nS (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x))

/-- Joint smoothness on the left and right archimedean root orbits. C11 of `sol-gate-theta`
uses this condition for mixed derivatives and differentiation under torus integrals. -/
def JointRootSmooth (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) : Prop :=
  ∀ g : P.tc.G, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) =>
      Ψ (nInf P p.1 * g * nInf P p.2))

/-- `n(ξ)` at the finite places, for rational `ξ`: `rat(n(ξ)) · n_∞(-ξ)`. -/
def nFin (P : CoverPackage D S H A) (ξ : F) : P.tc.G :=
  P.tc.rat (upperGL ξ) * nInf P (-(infEmbA ξ))

/-- `ψ_∞(ν x) = Π_w ψ_w(ν_w x_w)`. -/
def psiInf (ν : F) (x : InfinitePlace F → ℂ) : ℂ := ∏ w, psiC (w.embedding ν * x w)

/-- **def:torus-coefficient**: the `ν`-th Fourier coefficient along `N(F_∞)` over a fundamental
domain `Pd` of a period lattice. -/
def torusCoeff (P : CoverPackage D S H A) (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (Pd : Set (InfinitePlace F → ℂ)) (ν : F) : ℂ :=
  ((volume Pd).toReal)⁻¹ * ∫ x in Pd, Ψ (nInf P x * g) * psiInf (-ν) x

/-- `κ_F = vol(F\𝔸)` for `Π_v μ_v × Lebesgue`: the covolume `2^{-r}|d_F|^{1/2}` of `O_F ⊂ ℂ^r`. -/
def κF (F : Type) [Field F] [NumberField F] : ℝ :=
  (2 : ℝ) ^ (-(numComplex F : ℤ)) * Real.sqrt |(NumberField.discr F : ℝ)|

/-- `Π_{v ∉ T0} c_v(s)` (P-RES identifies it with `ζ_F^{T0}(6s)/ζ_F^{T0}(6s+1)`). -/
def cprod (T0 : Finset (FinPlace F)) (s : ℂ) : ℂ := ∏' v : {v : FinPlace F // v ∉ T0}, cv v.1 s

/-- The spherical vector of `I(T.weyl, -s)` at `v ∉ T0` (from `spherical_section`). -/
def sphWeyl (P : CoverPackage D S H A) (G : GlobalDatum P) (v : FinPlace F) (hv : v ∉ S.Sf)
    (s : ℂ) : (P.loc v).L → (G.T v).V :=
  (spherical_section (P.loc v) (P.tame v hv) (G.T v).weyl (G.B v hv).weyl
    (fun h => hv (S.over6 v h)) (-s)).choose

/-- **def:intertwined-scalar**: `Φ^M = κ_F⁻¹ · Π_{v∉T0} c_v(s) · scalar section of
`(M_v f_v)_{v∈T0} ⊗ (f°'_v)_{v∉T0} ⊗ (M_w f_w)_w`. -/
def scalarM (P : CoverPackage D S H A) (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G) : ℂ :=
  (κF F)⁻¹ * cprod Fs.T0 s *
    scalarOf P G (fun v => if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
        else sphWeyl P G v (fun h => hv (Fs.sub h)) s)
      (fun w => intertwineC (Fs.fC w)) g

/-- **def:whittaker-E**: the unfolded Whittaker coefficient
`W_E(g) = κ_F⁻¹ Σ_{δ ∈ F^×/Δ} Π_v lam_v(σ_v(a(δ)) 𝒥_v(π(g_v) f_v)) · Π_w 𝒥_w(π(g_w) f_w)`. -/
def whittakerE (P : CoverPackage D S H A) (G : GlobalDatum P) (μ : ∀ v : FinPlace F, LocHaar v)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G) : ℂ :=
  (κF F)⁻¹ * ∑' δ : Fˣ ⧸ G.Δ,
    (∏ᶠ v, G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
      (jacquet (P.loc v) A (μ v) (rtr (P.compF v (Function.surjInv P.q_surj g)) (Fs.f v))))) *
    ∏ w, jacquetC (rtr (P.compC w (Function.surjInv P.q_surj g)) (Fs.fC w))

/-- Rational Bruhat factorization with a Bstar left factor in both cells. -/
theorem rational_bruhat_factorization
    (P : CoverPackage D S H A) (G : GlobalDatum P) (g : GL (Fin 2) F) :
    (∃ (δ : Fˣ) (b : GL (Fin 2) F), b ∈ Bstar G ∧ g = b * diagGL δ) ∨
    (∃ (δ : Fˣ) (x : F) (b : GL (Fin 2) F),
      b ∈ Bstar G ∧ g = b * diagGL δ * weylGL * upperGL x) := by
  classical
  have hB (r : Fˣ) (x : F) : scalarGL r * upperGL x ∈ Bstar G := by
    change ((scalarGL r * upperGL x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ δ ∈ G.Δ, ((scalarGL r * upperGL x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (δ : F) * ((scalarGL r * upperGL x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1
    refine ⟨?_, 1, G.Δ.one_mem, ?_⟩ <;>
      simp [scalarGL, upperGL, Matrix.mul_apply, Fin.sum_univ_two]
  let a : F := g 0 0
  let b : F := g 0 1
  let c : F := g 1 0
  let d : F := g 1 1
  have hdet : a * d - b * c ≠ 0 := by
    simpa [a, b, c, d, Matrix.det_fin_two] using g.det_ne_zero
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by
      intro hd
      exact hdet (by simp [hc, hd])
    have ha : a ≠ 0 := by
      intro ha
      exact hdet (by simp [ha, hc])
    have hc0 : g 1 0 = 0 := hc
    have hd0 : g 1 1 ≠ 0 := hd
    let r : Fˣ := Units.mk0 d hd
    let δ : Fˣ := Units.mk0 (a / d) (div_ne_zero ha hd)
    let x : F := b / d
    refine Or.inl ⟨δ, scalarGL r * upperGL x, hB r x, ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scalarGL, upperGL, diagGL, r, δ, x, a, b, d, hc0,
        Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [hd0]
  · let x : F := a / c
    let t : F := d / c
    let yy : F := b / c - (a / c) * (d / c)
    have hy : yy ≠ 0 := by
      intro hy
      dsimp [yy] at hy
      field_simp [hc] at hy
      have hz : a * d - b * c = 0 := by linear_combination -hy
      exact hdet hz
    have hc0 : g 1 0 ≠ 0 := hc
    let r : Fˣ := Units.mk0 c hc
    let δ : Fˣ := Units.mk0 yy hy
    refine Or.inr ⟨δ, t, scalarGL r * upperGL x, hB r x, ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scalarGL, upperGL, diagGL, weylGL, r, δ, x, t, yy, a, b, c, d,
        Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp [hc0] <;> ring

/-- The rational Bruhat cells give exact representatives of the Bstar left quotient. -/
theorem rational_bruhat_coset_equiv
    (P : CoverPackage D S H A) (G : GlobalDatum P) :
    ∃ e : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) ≃
        Quotient (QuotientGroup.rightRel (Bstar G)),
      (∀ δ, e (Sum.inl δ) =
        Quotient.mk (QuotientGroup.rightRel (Bstar G)) (diagGL (Quotient.out δ))) ∧
      ∀ (δ : Fˣ ⧸ G.Δ) (x : F), e (Sum.inr (δ, x)) =
        Quotient.mk (QuotientGroup.rightRel (Bstar G))
          (diagGL (Quotient.out δ) * weylGL * upperGL x) := by
  classical
  let R : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) → GL (Fin 2) F :=
    Sum.elim (fun δ => diagGL (Quotient.out δ))
      (fun p => diagGL (Quotient.out p.1) * weylGL * upperGL p.2)
  let q : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) →
      Quotient (QuotientGroup.rightRel (Bstar G)) :=
    fun u => Quotient.mk (QuotientGroup.rightRel (Bstar G)) (R u)
  have hclass (a d : Fˣ ⧸ G.Δ) (b : GL (Fin 2) F)
      (hb : b ∈ Bstar G)
      (h00 : b 0 0 * ((Quotient.out a : Fˣ) : F) = ((Quotient.out d : Fˣ) : F))
      (h11 : b 1 1 = 1) : a = d := by
    rcases hb with ⟨_, t, ht, hdiag⟩
    have hd : ((Quotient.out d : Fˣ) : F) = (t : F) * ((Quotient.out a : Fˣ) : F) := by
      rw [hdiag, h11, mul_one] at h00
      exact h00.symm
    have hu : Quotient.out d * (Quotient.out a)⁻¹ = t := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      rw [hd, mul_assoc, mul_inv_cancel₀ (Quotient.out a).ne_zero, mul_one]
    have heq : (QuotientGroup.mk (Quotient.out d) : Fˣ ⧸ G.Δ) =
        QuotientGroup.mk (Quotient.out a) :=
      QuotientGroup.eq_iff_div_mem.mpr (by simpa only [div_eq_mul_inv, hu] using ht)
    simpa only [QuotientGroup.out_eq'] using heq.symm
  have hinj : Function.Injective q := by
    intro u v huv
    let b : GL (Fin 2) F := R v * (R u)⁻¹
    have hb : b ∈ Bstar G :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact huv)
    have hb10 : b 1 0 = 0 := hb.1
    have hf : b * R u = R v := by dsimp only [b]; group
    cases u with
    | inl a =>
      cases v with
      | inl d =>
        have h00 := congrArg (fun m : GL (Fin 2) F => m 0 0) hf
        have h11 := congrArg (fun m : GL (Fin 2) F => m 1 1) hf
        simp [R, diagGL, Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
        exact congrArg Sum.inl (hclass a d b hb h00 h11)
      | inr p =>
        have h10 := congrArg (fun m : GL (Fin 2) F => m 1 0) hf
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two, hb10] at h10
    | inr p =>
      cases v with
      | inl d =>
        have h10 := congrArg (fun m : GL (Fin 2) F => m 1 0) hf
        have h11 := congrArg (fun m : GL (Fin 2) F => m 1 1) hf
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two] at h10
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two, hb10, h10] at h11
      | inr r =>
        have h00 := congrArg (fun m : GL (Fin 2) F => m 0 0) hf
        have h01 := congrArg (fun m : GL (Fin 2) F => m 0 1) hf
        have h10 := congrArg (fun m : GL (Fin 2) F => m 1 0) hf
        have h11 := congrArg (fun m : GL (Fin 2) F => m 1 1) hf
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two] at h00 h10
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two, h00] at h01
        simp [R, diagGL, weylGL, upperGL, Matrix.mul_apply,
          Fin.sum_univ_two, hb10, h10] at h11
        exact congrArg Sum.inr (Prod.ext (hclass p.1 r.1 b hb h01 h10) h11)
  have hdiag_mul (a d : Fˣ) : diagGL (a * d) = diagGL a * diagGL d := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two]
  have hnormal (a : Fˣ) :
      ∃ b : GL (Fin 2) F, b ∈ Bstar G ∧
        diagGL a = b * diagGL (Quotient.out (QuotientGroup.mk a : Fˣ ⧸ G.Δ)) := by
    let d : Fˣ := Quotient.out (QuotientGroup.mk a : Fˣ ⧸ G.Δ)
    let t : Fˣ := a * d⁻¹
    have ht : t ∈ G.Δ := by
      have heq : (QuotientGroup.mk a : Fˣ ⧸ G.Δ) = QuotientGroup.mk d :=
        (QuotientGroup.out_eq' _).symm
      simpa only [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem.mp heq)
    refine ⟨diagGL t, ?_, ?_⟩
    · change (diagGL t : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        ∃ z ∈ G.Δ, (diagGL t : Matrix (Fin 2) (Fin 2) F) 0 0 =
          (z : F) * (diagGL t : Matrix (Fin 2) (Fin 2) F) 1 1
      exact ⟨by simp [diagGL], t, ht, by simp [diagGL]⟩
    · change diagGL a = diagGL t * diagGL d
      rw [← hdiag_mul]
      congr 1
      dsimp only [t]
      group
  have hsurj : Function.Surjective q := by
    intro β
    obtain hsmall | hbig := rational_bruhat_factorization P G (Quotient.out β)
    · obtain ⟨a, b, hb, hf⟩ := hsmall
      obtain ⟨c, hc, hn⟩ := hnormal a
      let δ : Fˣ ⧸ G.Δ := QuotientGroup.mk a
      refine ⟨Sum.inl δ, ?_⟩
      change Quotient.mk (QuotientGroup.rightRel (Bstar G))
        (diagGL (Quotient.out δ)) = β
      calc
        _ = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (Quotient.out β) := by
          apply Quotient.sound
          apply QuotientGroup.rightRel_apply.mpr
          rw [hf, hn]
          change b * (c * diagGL (Quotient.out δ)) * (diagGL (Quotient.out δ))⁻¹ ∈ Bstar G
          simpa only [mul_assoc, mul_inv_cancel, mul_one] using (Bstar G).mul_mem hb hc
        _ = β := Quotient.out_eq β
    · obtain ⟨a, x, b, hb, hf⟩ := hbig
      obtain ⟨c, hc, hn⟩ := hnormal a
      let δ : Fˣ ⧸ G.Δ := QuotientGroup.mk a
      refine ⟨Sum.inr (δ, x), ?_⟩
      change Quotient.mk (QuotientGroup.rightRel (Bstar G))
        (diagGL (Quotient.out δ) * weylGL * upperGL x) = β
      calc
        _ = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (Quotient.out β) := by
          apply Quotient.sound
          apply QuotientGroup.rightRel_apply.mpr
          rw [hf, hn]
          have heq : b * (c * diagGL (Quotient.out δ)) * weylGL * upperGL x *
              (diagGL (Quotient.out δ) * weylGL * upperGL x)⁻¹ = b * c := by group
          rw [heq]
          exact (Bstar G).mul_mem hb hc
        _ = β := Quotient.out_eq β
  refine ⟨Equiv.ofBijective q ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro δ
    rfl
  · intro δ x
    rfl

/-- Compare any ideal-lattice domain with a bounded measurable domain, including periodic integrals. -/
theorem ideal_periodic_domain_comparison (D : FieldData F)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume) :
    ∃ Pb : Set (InfinitePlace F → ℂ), MeasurableSet Pb ∧ IsCompact (closure Pb) ∧
      IsAddFundamentalDomain
        ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pb volume ∧
      volume Pd = volume Pb ∧ 0 < (volume Pb).toReal ∧
      ∀ f : (InfinitePlace F → ℂ) → ℂ,
        (∀ t ∈ ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom),
          ∀ x, f (t + x) = f x) → (∫ x in Pd, f x) = ∫ x in Pb, f x := by
  classical
  let : IsTotallyComplex F := D.isTotallyComplex
  let I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ := Units.mk0 𝔞 h𝔞
  let b₀ := mixedEmbedding.fractionalIdealLatticeBasis F I
  let e := ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv (F := F)
  let b := b₀.map e
  let j : mixedEmbedding.mixedSpace F →ₗ[ℤ] (InfinitePlace F → ℂ) :=
    e.toLinearMap.restrictScalars ℤ
  have hj (y : F) : j (mixedEmbedding F y) = infEmbA y := by
    ext w
    simp [j, e, ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv, infEmbA,
      mixedEmbedding]
  have hlat : (Submodule.span ℤ (Set.range b)).toAddSubgroup =
      (𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom := by
    have hrange : Set.range b = j '' Set.range b₀ := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b₀ i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    have hspanMap : Submodule.span ℤ (Set.range b) =
        (Submodule.span ℤ (Set.range b₀)).map j := by
      rw [hrange, ← Submodule.map_span]
    have hspan₀ : Submodule.span ℤ (Set.range b₀) = mixedEmbedding.idealLattice F I :=
      mixedEmbedding.span_idealLatticeBasis F I
    have hspan (x : InfinitePlace F → ℂ) :
        x ∈ Submodule.span ℤ (Set.range b) ↔
          ∃ y : F, y ∈ (I : Submodule (𝓞 F) F) ∧ infEmbA y = x := by
      rw [hspanMap, Submodule.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hspan₀] at hz
        obtain ⟨y, hy, rfl⟩ := (mixedEmbedding.mem_idealLattice F I).mp hz
        exact ⟨y, hy, hj y⟩
      · rintro ⟨y, hy, rfl⟩
        apply Submodule.mem_map.mpr
        refine ⟨mixedEmbedding F y, ?_, hj y⟩
        rw [hspan₀]
        exact (mixedEmbedding.mem_idealLattice F I).mpr ⟨y, hy, rfl⟩
    apply AddSubgroup.ext
    intro x
    change x ∈ Submodule.span ℤ (Set.range b) ↔
      x ∈ (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom
    rw [hspan]
    rfl
  let Pb := ZSpan.fundamentalDomain b
  have hcompact : IsCompact (closure Pb) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  have hfinite : volume Pb ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono subset_closure) hcompact.measure_lt_top).ne
  have hpositive : 0 < (volume Pb).toReal :=
    ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero b) hfinite
  let : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hPb : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup Pb volume :=
    ZSpan.isAddFundamentalDomain' b volume
  have hPd' : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range b)).toAddSubgroup Pd volume := by
    rw [hlat]
    exact hPd
  refine ⟨Pb, ZSpan.fundamentalDomain_measurableSet b, hcompact, ?_,
    hPd'.measure_eq hPb, hpositive, ?_⟩
  · rwa [hlat] at hPb
  · intro f hf
    apply hPd'.setIntegral_eq hPb
    intro t x
    change f ((t : InfinitePlace F → ℂ) + x) = f x
    exact hf t (by rw [← hlat]; exact t.property) x

/-- The complex-place covolume of a nonzero fractional ideal in the global Haar normalization. -/
theorem ideal_domain_covolume (D : FieldData F)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume) :
    (volume Pd).toReal = κF F * (FractionalIdeal.absNorm 𝔞 : ℝ) := by
  classical
  let : IsTotallyComplex F := D.isTotallyComplex
  let : IsEmpty {w : InfinitePlace F // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w.1)) w.2⟩
  let : IsProbabilityMeasure
      (volume : Measure ({w : InfinitePlace F // w.IsReal} → ℝ)) :=
    ⟨by simp [volume_pi]⟩
  let ec : {w : InfinitePlace F // w.IsComplex} ≃ InfinitePlace F :=
    { toFun := Subtype.val
      invFun := fun w => ⟨w, IsTotallyComplex.isComplex w⟩
      left_inv := fun w => by rfl
      right_inv := fun w => by rfl }
  let e := ArtinPrimitiveRoots.A1.Spec.complexPlaceLinearEquiv (F := F)
  let E := e.toContinuousLinearEquiv
  have he : MeasurePreserving E volume volume := by
    exact (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace F => ℂ) ec).comp
      measurePreserving_snd
  have hes : MeasurePreserving E.symm volume volume :=
    MeasurePreserving.symm E.toHomeomorph.toMeasurableEquiv he
  let I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ := Units.mk0 𝔞 h𝔞
  let L := mixedEmbedding.idealLattice F I
  let Lc := ZLattice.comap ℝ L E.symm.toLinearMap
  have hemb (y : F) : E (mixedEmbedding F y) = infEmbA y := by
    ext w
    rfl
  have hlat : Lc.toAddSubgroup =
      (𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom := by
    apply AddSubgroup.ext
    intro x
    change E.symm x ∈ mixedEmbedding.idealLattice F I ↔
      x ∈ (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom
    rw [mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨y, hy, heq⟩
      refine ⟨y, hy, ?_⟩
      have h := congrArg E heq
      change infEmbA y = x
      simpa only [hemb, E.apply_symm_apply] using h
    · rintro ⟨y, hy, heq⟩
      refine ⟨y, hy, ?_⟩
      apply E.injective
      change infEmbA y = x at heq
      simpa only [hemb, E.apply_symm_apply] using heq
  have hfd : IsAddFundamentalDomain Lc Pd volume := by
    change IsAddFundamentalDomain Lc.toAddSubgroup Pd volume
    rw [hlat]
    exact hPd
  have hn : NumberField.InfinitePlace.nrComplexPlaces F = numComplex F := Fintype.card_congr ec
  calc
    (volume Pd).toReal = ZLattice.covolume Lc volume := by
      simpa only [measureReal_def] using
        (ZLattice.covolume_eq_measure_fundamentalDomain Lc volume hfd).symm
    _ = ZLattice.covolume L volume := ZLattice.covolume_comap L volume volume hes
    _ = (FractionalIdeal.absNorm 𝔞 : ℝ) * (2⁻¹ : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
        Real.sqrt |(NumberField.discr F : ℝ)| := by
      exact mixedEmbedding.covolume_idealLattice F I
    _ = κF F * (FractionalIdeal.absNorm 𝔞 : ℝ) := by
      simp only [κF, hn, zpow_neg, zpow_natCast, inv_pow]
      ring

/-- Finite translation fixation and rational automorphy imply ideal periodicity at infinity. -/
theorem eisenstein_ideal_periodic
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h) :
    ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x : InfinitePlace F → ℂ,
      eisenstein P G Fs (nInf P (infEmbA ξ + x) * g) =
        eisenstein P G Fs (nInf P x * g) := by
  classical
  have hupper (a b : ℂ) : upperM ℂ a * upperM ℂ b = upperM ℂ b * upperM ℂ a := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hcomm (ξ : F) (x : InfinitePlace F → ℂ) :
      P.tc.rat (upperGL ξ) * nInf P x = nInf P x * P.tc.rat (upperGL ξ) := by
    obtain ⟨r, hq, hf, hc⟩ := P.nS_components
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
    have hf1 (v : FinPlace F) : P.compF v r = 1 := by
      simpa using hf v
    have hRP : P.ratRP (upperGL ξ) * r = r * P.ratRP (upperGL ξ) := by
      apply P.comp_ext
      · intro v
        simp only [map_mul, hf1, mul_one, one_mul]
      · intro w
        have hu : Matrix.GeneralLinearGroup.map w.embedding (upperGL ξ) =
            upperM ℂ (w.embedding ξ) := by
          apply Units.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.GeneralLinearGroup.map, upperGL, upperM]
        rw [map_mul, map_mul, P.compC_ratRP, hc, hu]
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg (fun a : GL (Fin 2) ℂ => (QuotientGroup.mk a : PGL2 ℂ))
          (hupper (w.embedding ξ) (x w))
    have h := congrArg P.q hRP
    simpa only [map_mul, P.q_ratRP, hq, nInf] using h
  have hni (x y : InfinitePlace F → ℂ) : nInf P (x + y) = nInf P x * nInf P y := by
    dsimp only [nInf]
    have hp : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y) =
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x) +
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y) := by simp
    rw [hp, ofAdd_add, map_mul]
  have hrat (ξ : F) : P.tc.rat (upperGL ξ) * P.tc.rat (upperGL (-ξ)) = 1 := by
    have hu : upperGL ξ * upperGL (-ξ) = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [upperGL, Matrix.mul_apply, Fin.sum_univ_two]
    rw [← map_mul, hu, map_one]
  intro ξ hξ x
  have hk : ∀ h, scalarOf P G Fs.f Fs.fC
      (h * (g⁻¹ * nFin P (-ξ) * g)) = scalarOf P G Fs.f Fs.fC h :=
    hfix (-ξ) ((𝔞 : Submodule (𝓞 F) F).neg_mem hξ)
  have hfactor : P.tc.rat (upperGL ξ) *
      (nInf P x * g * (g⁻¹ * nFin P (-ξ) * g)) =
        nInf P (infEmbA ξ + x) * g := by
    simp only [nFin, map_neg, neg_neg]
    calc
      P.tc.rat (upperGL ξ) * (nInf P x * g *
          (g⁻¹ * (P.tc.rat (upperGL (-ξ)) * nInf P (infEmbA ξ)) * g)) =
          P.tc.rat (upperGL ξ) * nInf P x * P.tc.rat (upperGL (-ξ)) *
            nInf P (infEmbA ξ) * g := by group
      _ = nInf P x * (P.tc.rat (upperGL ξ) * P.tc.rat (upperGL (-ξ))) *
          nInf P (infEmbA ξ) * g := by
        rw [hcomm]
        group
      _ = nInf P x * nInf P (infEmbA ξ) * g := by rw [hrat, mul_one]
      _ = nInf P (infEmbA ξ + x) * g := by rw [← hni, add_comm]
  calc
    eisenstein P G Fs (nInf P (infEmbA ξ + x) * g) =
        eisenstein P G Fs (P.tc.rat (upperGL ξ) *
          (nInf P x * g * (g⁻¹ * nFin P (-ξ) * g))) := by rw [hfactor]
    _ = eisenstein P G Fs (nInf P x * g * (g⁻¹ * nFin P (-ξ) * g)) :=
      (eisenstein_automorphic P G hs Fs).1 _ _
    _ = eisenstein P G Fs (nInf P x * g) :=
      (eisenstein_automorphic P G hs Fs).2.2 _ hk _

/-- Scalar cusp bounds are uniform under archimedean unipotent translation. -/
theorem scalar_cusp_height_majorant_unipotent
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) {ι : Type} [Fintype ι]
    (c : ι → Matrix.SpecialLinearGroup (Fin 2) F)
    (δ : ι → Fˣ) (r : P.RP) :
    ∃ Z : (InfinitePlace F → ℂ) → ArtinPrimitiveRoots.A1.Spec.X F,
      Continuous Z ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∀ (x : InfinitePlace F → ℂ) (i : ι)
          (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)),
          ‖scalarOf P G Fs.f Fs.fC
            (P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL
              (c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) *
                nInf P x * P.q r)‖ ≤
            C * ArtinPrimitiveRoots.A1.Spec.normHeight F
              ((c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • Z x) ^
                (1 + 2 * s.re) := by
  classical
  choose Cw hCw hbound using fun w =>
    sectionC_norm_majorant s (Fs.fC w) (Fs.fC_sec w).1 (Fs.fC_sec w).2
  obtain ⟨Z, hZ, hz⟩ := complex_spherical_height_product_unipotent (fun w => P.compC w r)
  obtain ⟨Cf, hCf, hfbound⟩ := finite_scalar_integral_translate_bound P G Fs
    (fun i => diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (c i)) r
  choose rn hqn hfn hcn using fun x : InfinitePlace F → ℂ =>
    P.nS_components ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  have hfn1 (x : InfinitePlace F → ℂ) (v : FinPlace F) : P.compF v (rn x) = 1 := by
    simpa using hfn x v
  let t (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) :=
    c i * ArtinPrimitiveRoots.A1.Spec.toSLF F γ
  let R (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) : P.RP :=
    P.ratRP (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) * rn x * r
  let y (i : ι) (w : InfinitePlace F) : ℂˣ := Units.map w.embedding.toMonoidHom (δ i)
  let U (w : InfinitePlace F) (a : Matrix.SpecialLinearGroup (Fin 2) F)
      (x : InfinitePlace F → ℂ) : PGL2 ℂ :=
    QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL
      (ArtinPrimitiveRoots.A1.Spec.toInf F a w)) * nC (x w) * P.compC w r
  let A (i : ι) (w : InfinitePlace F) : ℝ :=
    ‖(Complex.normSq (y i w : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)‖ * Cw w
  let Ai (i : ι) : ℝ := ∏ w, A i w
  have hA (i : ι) (w : InfinitePlace F) : 0 ≤ A i w :=
    mul_nonneg (norm_nonneg _) (hCw w)
  have hAi (i : ι) : 0 ≤ Ai i := Finset.prod_nonneg fun w _ => hA i w
  have hdiag (i : ι) (w : InfinitePlace F) :
      Matrix.GeneralLinearGroup.map w.embedding (diagGL (δ i)) = diagM ℂ (y i w) := by
    apply Units.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.GeneralLinearGroup.map, diagGL, diagM, y]
  have hsl (w : InfinitePlace F) (a : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix.GeneralLinearGroup.map w.embedding (Matrix.SpecialLinearGroup.toGL a) =
        Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toInf F a w) := by
    apply Units.ext
    rfl
  have hcomp (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      P.compC w (R i γ x) = QuotientGroup.mk (diagM ℂ (y i w)) * U w (t i γ) x := by
    simp only [R, U, map_mul, P.compC_ratRP, hdiag, hsl,
      QuotientGroup.mk_mul, hcn, nC, mul_assoc]
  have hcompF (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) (v : FinPlace F) :
      P.compF v (R i γ x) = P.compF v
        (P.ratRP (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) * r) := by
    simp only [R, map_mul, hfn1, mul_one]
  have hzero : upperM ℂ 0 = 1 := by
    apply Units.ext
    ext a b
    fin_cases a <;> fin_cases b <;> simp [upperM]
  have hsec (w : InfinitePlace F) (a : ℂˣ) (k : PGL2 ℂ) :
      Fs.fC w (QuotientGroup.mk (diagM ℂ a) * k) =
        (Complex.normSq (a : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s) * Fs.fC w k := by
    simpa only [hzero, QuotientGroup.mk_one, one_mul] using (Fs.fC_sec w).1 0 a k
  have hlocal (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      ‖Fs.fC w (P.compC w (R i γ x))‖ ≤
        A i w * ‖sphC (s.re : ℂ) (U w (t i γ) x)‖ := by
    rw [hcomp, hsec, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbound w (U w (t i γ) x))
      (norm_nonneg _)).trans_eq (by dsimp [A]; ring)
  have hheight (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) :
      (∏ w, ‖sphC (s.re : ℂ) (U w (t i γ) x)‖) =
        ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • Z x) ^ (1 + 2 * s.re) :=
    hz s.re (t i γ) x
  have hheight_nonneg (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) :
      0 ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • Z x) ^ (1 + 2 * s.re) := by
    rw [← hheight]
    exact Finset.prod_nonneg fun w _ => norm_nonneg _
  have hinf (i : ι) (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      (x : InfinitePlace F → ℂ) :
      (∏ w, ‖Fs.fC w (P.compC w (R i γ x))‖) ≤
        Ai i * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • Z x) ^ (1 + 2 * s.re) := by
    calc
      _ ≤ ∏ w, A i w * ‖sphC (s.re : ℂ) (U w (t i γ) x)‖ :=
        Finset.prod_le_prod₀ (fun w _ => norm_nonneg _) (fun w _ => hlocal i γ x w)
      _ = _ := by rw [Finset.prod_mul_distrib, hheight]
  refine ⟨Z, hZ, Cf * ∑ i, Ai i, mul_nonneg hCf (Finset.sum_nonneg fun i _ => hAi i), ?_⟩
  intro x i γ
  have hq : P.q (R i γ x) =
      P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) *
        nInf P x * P.q r := by
    simp only [R, map_mul, P.q_ratRP, hqn, nInf]
  change ‖scalarOf P G Fs.f Fs.fC
    (P.tc.rat (diagGL (δ i) * Matrix.SpecialLinearGroup.toGL (t i γ)) *
      nInf P x * P.q r)‖ ≤ _
  rw [← hq, (scalarOf_q P G Fs (R i γ x)).2, norm_mul, norm_prod]
  have hf : ‖∏ᶠ v, G.lam v (Fs.f v (P.compF v (R i γ x)))‖ ≤ Cf := by
    simp only [hcompF]
    simpa only [t, map_mul, mul_assoc] using hfbound i γ
  calc
    _ ≤ Cf * (Ai i * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • Z x) ^
        (1 + 2 * s.re)) :=
      mul_le_mul hf (hinf i γ x) (Finset.prod_nonneg fun w _ => norm_nonneg _) hCf
    _ = (Cf * Ai i) * ArtinPrimitiveRoots.A1.Spec.normHeight F ((t i γ) • Z x) ^
        (1 + 2 * s.re) := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun a _ => hAi a) (Finset.mem_univ i)) hCf)
      (hheight_nonneg i γ x)

/-- One finite torus family supports cusp representatives for all archimedean translations. -/
theorem finite_supported_cusp_representatives_unipotent
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
    {ι : Type} [Fintype ι] (σ : ι → Matrix.SpecialLinearGroup (Fin 2) F)
    (hσ : Function.Surjective
      (fun p : (Σ i, ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) =>
        Quotient.mk
          (QuotientGroup.rightRel (ArtinPrimitiveRoots.A1.Spec.borelSL F))
          ((σ p.1)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
            ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))))
    (r : P.RP) :
    ∃ U : Set (Fˣ ⧸ G.Δ), U.Finite ∧
      ∀ (x : InfinitePlace F → ℂ) (β : Quotient (QuotientGroup.rightRel (Bstar G))),
        scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * nInf P x * P.q r) ≠ 0 →
        ∃ (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i))
          (δ : Fˣ ⧸ G.Δ), δ ∈ U ∧
            β = Quotient.mk (QuotientGroup.rightRel (Bstar G))
              (diagGL (Quotient.out δ) * Matrix.SpecialLinearGroup.toGL
                ((σ i)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
                  ((q.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))) := by
  classical
  obtain ⟨U, hU, hsupport⟩ := finite_integral_translate_torus_support P G Fs
    (fun i => Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹)) r
  have hdiag_mul (a d : Fˣ) : diagGL (a * d) = diagGL a * diagGL d := by
    apply Units.ext
    ext j l
    fin_cases j <;> fin_cases l <;>
      simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two]
  have hdiag_mem (a : Fˣ) (ha : a ∈ G.Δ) : diagGL a ∈ Bstar G := by
    change (diagGL a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ d ∈ G.Δ, (diagGL a : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (d : F) * (diagGL a : Matrix (Fin 2) (Fin 2) F) 1 1
    exact ⟨by simp [diagGL], a, ha, by simp [diagGL]⟩
  have hcomp (a : Fˣ) (x : P.RP) (v : FinPlace F) :
      P.compF v (P.ratRP (diagGL a) * x) =
        (P.loc v).a (toLoc v a) * P.compF v x := by
    have hdiag : Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (diagGL a) = diagM (v.adicCompletion F) (toLoc v a) := by
      apply Units.ext
      ext j l
      fin_cases j <;> fin_cases l <;>
        simp [Matrix.GeneralLinearGroup.map, diagGL, diagM, toLoc]
    rw [map_mul, P.compF_ratRP, hdiag, ← (P.loc v).sec_a]
  refine ⟨U, hU, ?_⟩
  intro ξ β hβ
  obtain ⟨rn, hqn, hfn, _⟩ := P.nS_components
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), ξ)
  have hfn1 (v : FinPlace F) : P.compF v rn = 1 := by
    simpa using hfn v
  obtain ⟨i, q, a, b, hb, hfactor⟩ :=
    rational_cusp_factorization P G Γ σ hσ (Quotient.out β)
  let γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) := (q.out : Γ)
  let k : GL (Fin 2) F := Matrix.SpecialLinearGroup.toGL
    ((σ i)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F γ)
  let δ : Fˣ ⧸ G.Δ := QuotientGroup.mk a
  let d : Fˣ := Quotient.out δ
  let e : Fˣ := a * d⁻¹
  have he : e ∈ G.Δ := by
    have heq : (QuotientGroup.mk a : Fˣ ⧸ G.Δ) = QuotientGroup.mk d :=
      (QuotientGroup.out_eq' δ).symm
    simpa only [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem.mp heq)
  let b' : GL (Fin 2) F := b * diagGL e
  have hb' : b' ∈ Bstar G := (Bstar G).mul_mem hb (hdiag_mem e he)
  have had : a = e * d := by dsimp only [e]; group
  have hfactor' : Quotient.out β = b' * (diagGL d * k) := by
    change Quotient.out β = b * diagGL a * k at hfactor
    rw [hfactor, had, hdiag_mul]
    dsimp only [b']
    group
  have hscalar :
      scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * nInf P ξ * P.q r) =
        scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL d * k) * nInf P ξ * P.q r) := by
    rw [hfactor', map_mul]
    simpa only [mul_assoc] using (scalarOf_invariance P G Fs).1 b' hb'
      (P.tc.rat (diagGL d * k) * nInf P ξ * P.q r)
  let x : P.RP := P.ratRP k * rn * r
  let y : P.RP := P.ratRP (diagGL d) * x
  have hq : P.q y = P.tc.rat (diagGL d * k) * nInf P ξ * P.q r := by
    simp only [y, x, map_mul, P.q_ratRP, hqn, nInf, mul_assoc]
  have hnonzero : scalarOf P G Fs.f Fs.fC (P.q y) ≠ 0 := by
    rw [hq]
    exact fun h => hβ (hscalar.trans h)
  rw [(scalarOf_q P G Fs y).2] at hnonzero
  have hfinite :
      (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v d) * P.compF v x))) ≠ 0 := by
    simpa only [y, hcomp] using (mul_ne_zero_iff.mp hnonzero).1
  have hxfin (v : FinPlace F) :
      P.compF v x = P.compF v (P.ratRP k * r) := by
    simp only [x, map_mul, hfn1, mul_one]
  have hk : k = Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹) *
      Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toSLF F γ) := by
    dsimp only [k]
    rw [map_mul]
  have hδ : δ ∈ U := by
    apply hsupport i γ
    change (∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v d) *
      P.compF v (P.ratRP (Matrix.SpecialLinearGroup.toGL ((σ i)⁻¹) *
        Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.toSLF F γ)) * r)))) ≠ 0
    simpa only [hxfin, hk] using hfinite
  refine ⟨i, q, δ, hδ, ?_⟩
  change β = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (diagGL d * k)
  calc
    β = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (Quotient.out β) :=
      (Quotient.out_eq β).symm
    _ = _ := by
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      rw [hfactor']
      simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using (Bstar G).inv_mem hb'

/-- Eisenstein summands admit a summable majorant uniform on compact archimedean sets. -/
theorem eisenstein_majorant_on_compact
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K) :
    ∃ M : Quotient (QuotientGroup.rightRel (Bstar G)) → ℝ,
      Summable M ∧ (∀ β, 0 ≤ M β) ∧ ∀ x ∈ K, ∀ β,
        ‖scalarOf P G Fs.f Fs.fC
          (P.tc.rat (Quotient.out β) * nInf P x * g)‖ ≤ M β := by
  classical
  by_cases hKe : K = ∅
  · subst K
    refine ⟨fun _ => 0, summable_zero, fun _ => le_rfl, ?_⟩
    simp
  obtain ⟨x0, hx0⟩ := Set.nonempty_iff_ne_empty.mpr hKe
  let : IsTotallyComplex F := D.isTotallyComplex
  let Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) := ⊤
  let : Γ.FiniteIndex := by dsimp only [Γ]; infer_instance
  obtain ⟨ι, hι, σ, hσ⟩ := ArtinPrimitiveRoots.A1.Spec.exists_cusp_reps F Γ
  let : Fintype ι := hι
  obtain ⟨r, rfl⟩ := P.q_surj g
  obtain ⟨U, hU, hcover⟩ :=
    finite_supported_cusp_representatives_unipotent P G Fs Γ σ hσ.2 r
  let : Fintype U := hU.fintype
  let J := U × ι
  obtain ⟨Z, hZ, C0, hC0, hscalar⟩ := scalar_cusp_height_majorant_unipotent P G Fs
    (fun j : J => (σ j.2)⁻¹) (fun j : J => Quotient.out j.1.1) r
  choose m hm hmbound using fun i =>
    ArtinPrimitiveRoots.A1.Spec.eisSeries_majorant F Γ (σ i)
      (Z '' K) (hK.image hZ) s.re s.re hs
  have hm_bound (x : InfinitePlace F → ℂ) (hx : x ∈ K) (i : ι)
      (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) :
      ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ i) (s.re : ℂ) (Z x) q‖ ≤ m i q := by
    exact hmbound i (Z x) (Set.mem_image_of_mem Z hx) (s.re : ℂ) (by simp) (by simp) q
  have hm_nonneg (i : ι) (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ i)) :
      0 ≤ m i q := (norm_nonneg _).trans (hm_bound x0 hx0 i q)
  let Ξ := Σ j : J, ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ (σ j.2)
  let weight : Ξ → ℝ := fun p => C0 * m p.1.2 p.2
  have hweight_nonneg (p : Ξ) : 0 ≤ weight p := mul_nonneg hC0 (hm_nonneg p.1.2 p.2)
  have hweight : Summable weight := by
    apply (summable_sigma_of_nonneg hweight_nonneg).2
    constructor
    · intro j
      exact (hm j.2).mul_left C0
    · exact (hasSum_fintype _).summable
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  let V : Set Q := {β | ∃ x ∈ K,
    scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * nInf P x * P.q r) ≠ 0}
  let a (p : Ξ) : GL (Fin 2) F :=
    diagGL (Quotient.out p.1.1.1) * Matrix.SpecialLinearGroup.toGL
      ((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
        ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
  let ret : Ξ → Q := fun p => Quotient.mk (QuotientGroup.rightRel (Bstar G)) (a p)
  have hparam : ∀ β : V, ∃ p : Ξ, ret p = β.1 := by
    intro β
    obtain ⟨x, _, hn⟩ := β.property
    obtain ⟨i, q, δ, hδ, heq⟩ := hcover x β.1 hn
    exact ⟨⟨(⟨δ, hδ⟩, i), q⟩, heq.symm⟩
  choose φ hφ using hparam
  have hφinj : Function.Injective φ := by
    intro β η heq
    apply Subtype.ext
    calc
      β.1 = ret (φ β) := (hφ β).symm
      _ = ret (φ η) := congrArg ret heq
      _ = η.1 := hφ η
  let majorant : Q → ℝ := fun β => if h : β ∈ V then weight (φ ⟨β, h⟩) else 0
  have hmajorant_sub : (fun β : V => majorant β.1) = fun β : V => weight (φ β) := by
    funext β
    simp only [majorant, dite_eq_left β.property]
  have hsupp : Summable (fun β : V => majorant β.1) := by
    rw [hmajorant_sub]
    exact hweight.comp_injective hφinj
  have hsupport : Function.support majorant ⊆ V := by
    intro β hβ
    by_contra h
    exact hβ (by simp only [majorant, dite_eq_right h])
  have hmajorant : Summable majorant :=
    ((hasSum_subtype_iff_of_support_subset (s := V) hsupport).1 hsupp.hasSum).summable
  have hmajorant_nonneg (β : Q) : 0 ≤ majorant β := by
    dsimp only [majorant]
    split_ifs with h
    · exact hweight_nonneg _
    · exact le_rfl
  have hrep (b d : GL (Fin 2) F) (hbd : QuotientGroup.rightRel (Bstar G) b d)
      (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat b * nInf P x * P.q r) =
        scalarOf P G Fs.f Fs.fC (P.tc.rat d * nInf P x * P.q r) := by
    have hd : d * b⁻¹ ∈ Bstar G := QuotientGroup.rightRel_apply.mp hbd
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (d * b⁻¹) hd
        (P.tc.rat b * nInf P x * P.q r)).symm
  have hterm (p : Ξ) (x : InfinitePlace F → ℂ) :
      ArtinPrimitiveRoots.A1.Spec.normHeight F
        (((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
          ((p.2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) • Z x) ^
          (1 + 2 * s.re) =
        ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ p.1.2) (s.re : ℂ) (Z x) p.2‖ := by
    let γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F) := (p.2.out : Γ)
    let y := ((σ p.1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • Z x
    have hpos : 0 < ArtinPrimitiveRoots.A1.Spec.normHeight F y := by
      apply Finset.prod_pos
      intro w _
      rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (y w)
    have hact : (σ p.1.2)⁻¹ • (γ • Z x) = y := by
      change (σ p.1.2)⁻¹ • ((ArtinPrimitiveRoots.A1.Spec.toSLF F γ) • Z x) = y
      exact (mul_smul _ _ _).symm
    change ArtinPrimitiveRoots.A1.Spec.normHeight F y ^ (1 + 2 * s.re) = _
    unfold ArtinPrimitiveRoots.A1.Spec.eisTerm
    change _ = ‖(ArtinPrimitiveRoots.A1.Spec.normHeight F
      ((σ p.1.2)⁻¹ • (γ • Z x)) : ℂ) ^ (1 + 2 * (s.re : ℂ))‖
    rw [hact, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hbound_support (x : InfinitePlace F → ℂ) (hx : x ∈ K) (β : V) :
      ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out β.1) * nInf P x * P.q r)‖ ≤ weight (φ β) := by
    have hcoset : QuotientGroup.rightRel (Bstar G) (Quotient.out β.1) (a (φ β)) := by
      apply Quotient.exact
      exact (Quotient.out_eq β.1).trans (hφ β).symm
    calc
      _ = ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (a (φ β)) * nInf P x * P.q r)‖ :=
        congrArg norm (hrep _ _ hcoset x)
      _ ≤ C0 * ArtinPrimitiveRoots.A1.Spec.normHeight F
          (((σ (φ β).1.2)⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F
            (((φ β).2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) • Z x) ^
            (1 + 2 * s.re) :=
        hscalar x (φ β).1 (((φ β).2.out : Γ) : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
      _ = C0 * ‖ArtinPrimitiveRoots.A1.Spec.eisTerm F Γ (σ (φ β).1.2)
          (s.re : ℂ) (Z x) (φ β).2‖ := congrArg (C0 * ·) (hterm (φ β) x)
      _ ≤ weight (φ β) := mul_le_mul_of_nonneg_left (hm_bound x hx _ _) hC0
  refine ⟨majorant, hmajorant, hmajorant_nonneg, ?_⟩
  intro x hx β
  by_cases hβ : β ∈ V
  · simpa only [majorant, dite_eq_left hβ] using hbound_support x hx ⟨β, hβ⟩
  · have hzero : scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out β) * nInf P x * P.q r) = 0 := by
      by_contra hn
      exact hβ ⟨x, hx, hn⟩
    simp only [hzero, norm_zero, majorant, dite_eq_right hβ, le_refl]

/-- Each rational scalar summand is continuous along the archimedean unipotent orbit. -/
theorem scalarOf_unipotent_continuous
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G)
    (γ : GL (Fin 2) F) :
    Continuous (fun x : InfinitePlace F → ℂ =>
      scalarOf P G Fs.f Fs.fC (P.tc.rat γ * nInf P x * g)) := by
  classical
  have hcancel (t : ℂ) : upperM ℂ t * upperM ℂ (-t) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, Matrix.mul_apply, Fin.sum_univ_two]
  have hinv (t : ℂ) : (upperM ℂ t)⁻¹ = upperM ℂ (-t) := by
    calc
      (upperM ℂ t)⁻¹ = (upperM ℂ t)⁻¹ * (upperM ℂ t * upperM ℂ (-t)) := by
        rw [hcancel, mul_one]
      _ = upperM ℂ (-t) := by group
  have hval : Continuous (fun t : ℂ => (upperM ℂ t : Matrix (Fin 2) (Fin 2) ℂ)) := by
    change Continuous (fun t : ℂ => (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ))
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first | exact continuous_const | exact continuous_id
  have hu : Continuous (upperM ℂ) := Units.continuous_iff.mpr ⟨hval, by
    simpa only [hinv, Function.comp_def] using
      hval.comp (continuous_neg : Continuous (fun t : ℂ => -t))⟩
  have hn : Continuous (nC : ℂ → PGL2 ℂ) := QuotientGroup.continuous_mk.comp hu
  obtain ⟨r, rfl⟩ := P.q_surj g
  choose rn hqn hfn hcn using fun x : InfinitePlace F → ℂ =>
    P.nS_components ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  have hfn1 (x : InfinitePlace F → ℂ) (v : FinPlace F) : P.compF v (rn x) = 1 := by
    simpa using hfn x v
  let R (x : InfinitePlace F → ℂ) : P.RP := P.ratRP γ * rn x * r
  let cf : ℂ := ∏ᶠ v, G.lam v (Fs.f v (P.compF v (P.ratRP γ * r)))
  have hq (x : InfinitePlace F → ℂ) :
      P.q (R x) = P.tc.rat γ * nInf P x * P.q r := by
    simp only [R, map_mul, P.q_ratRP, hqn, nInf]
  have hcompF (x : InfinitePlace F → ℂ) (v : FinPlace F) :
      P.compF v (R x) = P.compF v (P.ratRP γ * r) := by
    simp only [R, map_mul, hfn1, mul_one]
  have hcompC (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      P.compC w (R x) = P.compC w (P.ratRP γ) * nC (x w) * P.compC w r := by
    simp only [R, map_mul, hcn, nC]
  have hformula (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat γ * nInf P x * P.q r) =
        cf * ∏ w, Fs.fC w (P.compC w (P.ratRP γ) * nC (x w) * P.compC w r) := by
    rw [← hq, (scalarOf_q P G Fs (R x)).2]
    simp only [cf, hcompF, hcompC]
  have hprod : Continuous (fun x : InfinitePlace F → ℂ =>
      ∏ w, Fs.fC w (P.compC w (P.ratRP γ) * nC (x w) * P.compC w r)) := by
    apply continuous_finsetProd
    intro w _
    exact (Fs.fC_sec w).2.comp
      ((continuous_const.mul (hn.comp (continuous_apply w))).mul continuous_const)
  have hc : Continuous (fun x : InfinitePlace F → ℂ =>
      cf * ∏ w, Fs.fC w (P.compC w (P.ratRP γ) * nC (x w) * P.compC w r)) :=
    continuous_const.mul hprod
  exact hc.congr fun x => (hformula x).symm

/-- Compact majorants justify absolute termwise integration of the Eisenstein series. -/
theorem eisenstein_integral_tsum_on_compact
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBK : B ⊆ K) :
    (∀ β : Quotient (QuotientGroup.rightRel (Bstar G)),
      IntegrableOn (fun x => scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out β) * nInf P x * g)) B) ∧
    Summable (fun β : Quotient (QuotientGroup.rightRel (Bstar G)) =>
      ∫ x in B, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out β) * nInf P x * g)‖) ∧
    (∫ x in B, eisenstein P G Fs (nInf P x * g)) =
      ∑' β : Quotient (QuotientGroup.rightRel (Bstar G)),
        ∫ x in B, scalarOf P G Fs.f Fs.fC
          (P.tc.rat (Quotient.out β) * nInf P x * g) := by
  classical
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F)
    infer_instance
  let : Countable (GL (Fin 2) F) :=
    (Units.val_injective : Function.Injective
      (fun a : GL (Fin 2) F => (a : Matrix (Fin 2) (Fin 2) F))).countable
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  let f (β : Q) (x : InfinitePlace F → ℂ) : ℂ :=
    scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * nInf P x * g)
  have hint (β : Q) : IntegrableOn (f β) B := by
    exact (ContinuousOn.integrableOn_compact hK
      (scalarOf_unipotent_continuous P G Fs g (Quotient.out β)).continuousOn).mono_set hBK
  have hBlt : volume B < ⊤ := lt_of_le_of_lt (measure_mono hBK)
    (lt_top_iff_ne_top.mpr hK.measure_ne_top)
  let : IsFiniteMeasure (volume.restrict B) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hBlt⟩
  obtain ⟨M, hM, _, hbound⟩ := eisenstein_majorant_on_compact P G hs Fs g K hK
  have hnonneg (β : Q) : 0 ≤ ∫ x in B, ‖f β x‖ :=
    integral_nonneg fun x => norm_nonneg _
  have hboundint (β : Q) : (∫ x in B, ‖f β x‖) ≤ volume.real B * M β := by
    calc
      _ ≤ ∫ x in B, M β := integral_mono_ae (hint β).norm (integrable_const _) (by
        filter_upwards [ae_restrict_mem hB] with x hx
        exact hbound x (hBK hx) β)
      _ = _ := by rw [setIntegral_const, smul_eq_mul]
  have hsum : Summable (fun β : Q => ∫ x in B, ‖f β x‖) :=
    Summable.of_nonneg_of_le hnonneg hboundint (hM.mul_left (volume.real B))
  refine ⟨hint, hsum, ?_⟩
  simpa only [eisenstein, f, mul_assoc] using
    (integral_tsum_of_summable_integral_norm hint hsum).symm

/-- Integrating the Bruhat cells splits the absolutely convergent Eisenstein series. -/
theorem eisenstein_bruhat_integral_on_compact
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBK : B ⊆ K) :
    (∫ x in B, eisenstein P G Fs (nInf P x * g)) =
      (∑' δ : Fˣ ⧸ G.Δ, ∫ x in B, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ)) * nInf P x * g)) +
      ∑' p : (Fˣ ⧸ G.Δ) × F, ∫ x in B, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) *
          nInf P x * g) := by
  classical
  obtain ⟨_, habs, heq⟩ := eisenstein_integral_tsum_on_compact P G hs Fs g K hK B hB hBK
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  let I (β : Q) : ℂ := ∫ x in B, scalarOf P G Fs.f Fs.fC
    (P.tc.rat (Quotient.out β) * nInf P x * g)
  have hsum : Summable I := habs.of_norm_bounded fun β => norm_integral_le_integral_norm _
  obtain ⟨e, hsmall, hbig⟩ := rational_bruhat_coset_equiv P G
  let R : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) → GL (Fin 2) F :=
    Sum.elim (fun δ => diagGL (Quotient.out δ))
      (fun p => diagGL (Quotient.out p.1) * weylGL * upperGL p.2)
  have he (u) : e u = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (R u) := by
    cases u with
    | inl δ => exact hsmall δ
    | inr p => exact hbig p.1 p.2
  have hrep (u) : I (e u) = ∫ x in B, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (R u) * nInf P x * g) := by
    have hb : R u * (Quotient.out (e u))⁻¹ ∈ Bstar G :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact ((Quotient.out_eq (e u)).trans (he u)))
    apply integral_congr_ae
    filter_upwards [] with x
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (R u * (Quotient.out (e u))⁻¹) hb
        (P.tc.rat (Quotient.out (e u)) * (nInf P x * g))).symm
  have hsum' : Summable (fun u => I (e u)) := hsum.comp_injective e.injective
  calc
    _ = ∑' β : Q, I β := heq
    _ = ∑' u, I (e u) := (e.tsum_eq I).symm
    _ = (∑' δ, I (e (Sum.inl δ))) + ∑' p, I (e (Sum.inr p)) :=
      (hsum'.comp_injective Sum.inl_injective).tsum_sum
        (hsum'.comp_injective Sum.inr_injective)
    _ = _ := by
      congr 1
      · apply tsum_congr
        intro δ
        exact hrep (Sum.inl δ)
      · apply tsum_congr
        intro p
        exact hrep (Sum.inr p)

/-- A small-cell summand is unchanged by the archimedean unipotent variable. -/
theorem scalarOf_diag_unipotent
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (δ : Fˣ)
    (g : P.tc.G) (x : InfinitePlace F → ℂ) :
    scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL δ) * nInf P x * g) =
      scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL δ) * g) := by
  classical
  let y : InfinitePlace F → ℂ := infEmbA (δ : F) * x
  obtain ⟨r, hq, hf, hc⟩ := P.nS_components
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  obtain ⟨t, hqt, hft, hct⟩ := P.nS_components
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y)
  have hf1 (v : FinPlace F) : P.compF v r = 1 := by simpa using hf v
  have hft1 (v : FinPlace F) : P.compF v t = 1 := by simpa using hft v
  have hmat (w : InfinitePlace F) :
      Matrix.GeneralLinearGroup.map w.embedding (diagGL δ) * upperM ℂ (x w) =
        upperM ℂ (y w) * Matrix.GeneralLinearGroup.map w.embedding (diagGL δ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.map, diagGL, upperM, y, infEmbA,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hRP : P.ratRP (diagGL δ) * r = t * P.ratRP (diagGL δ) := by
    apply P.comp_ext
    · intro v
      simp only [map_mul, hf1, hft1, mul_one, one_mul]
    · intro w
      rw [map_mul, map_mul, P.compC_ratRP, hc, hct]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg (fun a : GL (Fin 2) ℂ => (QuotientGroup.mk a : PGL2 ℂ)) (hmat w)
  have hcomm : P.tc.rat (diagGL δ) * nInf P x = nInf P y * P.tc.rat (diagGL δ) := by
    simpa only [map_mul, P.q_ratRP, hq, hqt, nInf] using congrArg P.q hRP
  rw [hcomm, mul_assoc]
  exact (scalarOf_invariance P G Fs).2.1
    (Multiplicative.ofAdd ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y)) _

/-- The zero torus coefficient can be computed on a bounded measurable ideal domain. -/
theorem eisenstein_zeroCoeff_bounded_domain
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume) :
    ∃ Pb : Set (InfinitePlace F → ℂ), MeasurableSet Pb ∧ IsCompact (closure Pb) ∧
      IsAddFundamentalDomain
        ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pb volume ∧
      volume Pd = volume Pb ∧ 0 < (volume Pb).toReal ∧
      torusCoeff P (eisenstein P G Fs) g Pd 0 =
        torusCoeff P (eisenstein P G Fs) g Pb 0 := by
  classical
  obtain ⟨Pb, hmb, hcb, hdb, hvol, hpos, hint⟩ :=
    ideal_periodic_domain_comparison D 𝔞 h𝔞 Pd hPd
  have hperiodic : ∀ t ∈
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom),
      ∀ x : InfinitePlace F → ℂ,
      eisenstein P G Fs (nInf P (t + x) * g) = eisenstein P G Fs (nInf P x * g) := by
    intro t ht x
    rcases ht with ⟨ξ, hξ, rfl⟩
    exact eisenstein_ideal_periodic P G hs Fs g 𝔞 hfix ξ hξ x
  have hi := hint (fun x => eisenstein P G Fs (nInf P x * g)) hperiodic
  have hpsi0 (x : InfinitePlace F → ℂ) : psiInf (0 : F) x = 1 := by
    simp [psiInf, psiC]
  refine ⟨Pb, hmb, hcb, hdb, hvol, hpos, ?_⟩
  simp only [torusCoeff, neg_zero, hpsi0, mul_one, hvol, hi]

/-- The normalized zero coefficient has summable small- and big-cell contributions. -/
theorem eisenstein_zeroCoeff_bruhat_on_compact
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBK : B ⊆ K)
    (hvol : 0 < (volume B).toReal) :
    Summable (fun δ : Fˣ ⧸ G.Δ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out δ)) * g)) ∧
    Summable (fun p : (Fˣ ⧸ G.Δ) × F => ∫ x in B, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) *
        nInf P x * g)) ∧
    torusCoeff P (eisenstein P G Fs) g B 0 =
      (∑' δ : Fˣ ⧸ G.Δ, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ)) * g)) +
      ((volume B).toReal : ℂ)⁻¹ *
        ∑' p : (Fˣ ⧸ G.Δ) × F, ∫ x in B, scalarOf P G Fs.f Fs.fC
          (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) *
            nInf P x * g) := by
  classical
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  obtain ⟨e, hsmall, hbig⟩ := rational_bruhat_coset_equiv P G
  let R : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) → GL (Fin 2) F :=
    Sum.elim (fun δ => diagGL (Quotient.out δ))
      (fun p => diagGL (Quotient.out p.1) * weylGL * upperGL p.2)
  have he (u) : e u = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (R u) := by
    cases u with
    | inl δ => exact hsmall δ
    | inr p => exact hbig p.1 p.2
  have hrep (u) (h : P.tc.G) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out (e u)) * h) =
        scalarOf P G Fs.f Fs.fC (P.tc.rat (R u) * h) := by
    have hb : R u * (Quotient.out (e u))⁻¹ ∈ Bstar G :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact ((Quotient.out_eq (e u)).trans (he u)))
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (R u * (Quotient.out (e u))⁻¹) hb
        (P.tc.rat (Quotient.out (e u)) * h)).symm
  have hsum : Summable (fun β : Q => scalarOf P G Fs.f Fs.fC
      (P.tc.rat (Quotient.out β) * g)) :=
    (eisenstein_summable P G hs Fs g).of_norm_bounded fun _ => le_rfl
  have hsmallSum : Summable (fun δ : Fˣ ⧸ G.Δ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out δ)) * g)) :=
    (hsum.comp_injective (e.injective.comp Sum.inl_injective)).congr
      (fun δ => hrep (Sum.inl δ) g)
  obtain ⟨_, habs, _⟩ := eisenstein_integral_tsum_on_compact P G hs Fs g K hK B hB hBK
  let I (β : Q) : ℂ := ∫ x in B, scalarOf P G Fs.f Fs.fC
    (P.tc.rat (Quotient.out β) * nInf P x * g)
  have hsumI : Summable I := habs.of_norm_bounded fun _ => norm_integral_le_integral_norm _
  have hrepI (p : (Fˣ ⧸ G.Δ) × F) : I (e (Sum.inr p)) =
      ∫ x in B, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) * nInf P x * g) := by
    apply integral_congr_ae
    filter_upwards [] with x
    simpa only [R, Sum.elim_inr, mul_assoc] using hrep (Sum.inr p) (nInf P x * g)
  have hbigSum : Summable (fun p : (Fˣ ⧸ G.Δ) × F => ∫ x in B, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) * nInf P x * g)) :=
    (hsumI.comp_injective (e.injective.comp Sum.inr_injective)).congr hrepI
  have hsmallIntegral (δ : Fˣ ⧸ G.Δ) :
      (∫ x in B, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ)) * nInf P x * g)) =
      ((volume B).toReal : ℂ) * scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ)) * g) := by
    simp_rw [scalarOf_diag_unipotent P G Fs]
    rw [setIntegral_const, Complex.real_smul]
    rfl
  have hvolC : ((volume B).toReal : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hvol
  have hpsi0 (x : InfinitePlace F → ℂ) : psiInf (0 : F) x = 1 := by
    simp [psiInf, psiC]
  refine ⟨hsmallSum, hbigSum, ?_⟩
  simp only [torusCoeff, Complex.ofReal_inv, neg_zero, hpsi0, mul_one]
  rw [eisenstein_bruhat_integral_on_compact P G hs Fs g K hK B hB hBK]
  simp_rw [hsmallIntegral]
  rw [tsum_mul_left, mul_add, ← mul_assoc, inv_mul_cancel₀ hvolC, one_mul]

/-- A fixed finite rational period becomes an archimedean translation in a scalar summand. -/
theorem scalarOf_rational_period_translate
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G)
    (γ : GL (Fin 2) F) (α : F) (x : InfinitePlace F → ℂ)
    (hfix : ∀ h, scalarOf P G Fs.f Fs.fC
      (h * (g⁻¹ * nFin P α * g)) = scalarOf P G Fs.f Fs.fC h) :
    scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL α) * nInf P x * g) =
      scalarOf P G Fs.f Fs.fC
        (P.tc.rat γ * nInf P (infEmbA α + x) * g) := by
  classical
  have hupper (a b : ℂ) : upperM ℂ a * upperM ℂ b = upperM ℂ b * upperM ℂ a := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hcomm (y : InfinitePlace F → ℂ) :
      P.tc.rat (upperGL α) * nInf P y = nInf P y * P.tc.rat (upperGL α) := by
    obtain ⟨r, hq, hf, hc⟩ := P.nS_components
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y)
    have hf1 (v : FinPlace F) : P.compF v r = 1 := by simpa using hf v
    have hRP : P.ratRP (upperGL α) * r = r * P.ratRP (upperGL α) := by
      apply P.comp_ext
      · intro v
        simp only [map_mul, hf1, mul_one, one_mul]
      · intro w
        have hu : Matrix.GeneralLinearGroup.map w.embedding (upperGL α) =
            upperM ℂ (w.embedding α) := by
          apply Units.ext
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.GeneralLinearGroup.map, upperGL, upperM]
        rw [map_mul, map_mul, P.compC_ratRP, hc, hu]
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        exact congrArg (fun a : GL (Fin 2) ℂ => (QuotientGroup.mk a : PGL2 ℂ))
          (hupper (w.embedding α) (y w))
    simpa only [map_mul, P.q_ratRP, hq, nInf] using congrArg P.q hRP
  have hni (y z : InfinitePlace F → ℂ) : nInf P (y + z) = nInf P y * nInf P z := by
    dsimp only [nInf]
    have hp : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y + z) =
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y) +
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), z) := by simp
    rw [hp, ofAdd_add, map_mul]
  have hy : (infEmbA α + x) + (-infEmbA α) = x := by abel
  have hfactor : (P.tc.rat γ * nInf P (infEmbA α + x) * g) *
      (g⁻¹ * nFin P α * g) = P.tc.rat (γ * upperGL α) * nInf P x * g := by
    dsimp only [nFin]
    calc
      _ = P.tc.rat γ * (nInf P (infEmbA α + x) * P.tc.rat (upperGL α)) *
          nInf P (-infEmbA α) * g := by group
      _ = P.tc.rat γ * (P.tc.rat (upperGL α) * nInf P (infEmbA α + x)) *
          nInf P (-infEmbA α) * g := by rw [← hcomm]
      _ = (P.tc.rat γ * P.tc.rat (upperGL α)) *
          (nInf P (infEmbA α + x) * nInf P (-infEmbA α)) * g := by group
      _ = (P.tc.rat γ * P.tc.rat (upperGL α)) * nInf P x * g := by rw [← hni, hy]
      _ = _ := by rw [map_mul]
  simpa only [hfactor] using hfix (P.tc.rat γ * nInf P (infEmbA α + x) * g)

/-- Summable translated-domain norm integrals justify global integration over an ideal lattice. -/
theorem ideal_domain_integral_tiling
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (_hB : MeasurableSet B) (hBK : B ⊆ K)
    (hBd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) B volume)
    (f : (InfinitePlace F → ℂ) → ℂ) (hf : Continuous f)
    (hsum : Summable (fun ξ : (𝔞 : Submodule (𝓞 F) F).toAddSubgroup =>
      ∫ x in B, ‖f (infEmbA (ξ : F) + x)‖)) :
    Integrable f ∧
      (∫ x : InfinitePlace F → ℂ, f x) =
        ∑' ξ : (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
          ∫ x in B, f (infEmbA (ξ : F) + x) := by
  classical
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let H := (𝔞 : Submodule (𝓞 F) F).toAddSubgroup
  let L := H.map (infEmbA (F := F)).toAddMonoidHom
  let e : H ≃+ L := H.equivMapOfInjective (infEmbA (F := F)).toAddMonoidHom
    (infEmbA (F := F)).injective
  let : Countable L := e.symm.injective.countable
  have heval (ξ : H) : (e ξ : InfinitePlace F → ℂ) = infEmbA (ξ : F) := rfl
  have hint (ξ : H) : IntegrableOn
      (fun x : InfinitePlace F → ℂ => f (infEmbA (ξ : F) + x)) B := by
    exact (ContinuousOn.integrableOn_compact hK
      (hf.comp (continuous_const.add continuous_id)).continuousOn).mono_set hBK
  have hlin : (∫⁻ x : InfinitePlace F → ℂ, ENNReal.ofReal ‖f x‖) =
      ∑' ξ : H, ∫⁻ x in B, ENNReal.ofReal ‖f (infEmbA (ξ : F) + x)‖ := by
    calc
      _ = ∑' t : L, ∫⁻ x in B, ENNReal.ofReal ‖f ((t : InfinitePlace F → ℂ) + x)‖ :=
        hBd.lintegral_eq_tsum'' (fun x => ENNReal.ofReal ‖f x‖)
      _ = ∑' ξ : H, ∫⁻ x in B, ENNReal.ofReal ‖f ((e ξ : InfinitePlace F → ℂ) + x)‖ :=
        (e.toEquiv.tsum_eq _).symm
      _ = _ := by simp only [heval]
  have hnormint (ξ : H) :
      (∫⁻ x in B, ENNReal.ofReal ‖f (infEmbA (ξ : F) + x)‖) =
        ENNReal.ofReal (∫ x in B, ‖f (infEmbA (ξ : F) + x)‖) :=
    (ofReal_integral_eq_lintegral_ofReal (hint ξ).norm
      (Filter.Eventually.of_forall fun x => norm_nonneg _)).symm
  have hnonneg (ξ : H) : 0 ≤ ∫ x in B, ‖f (infEmbA (ξ : F) + x)‖ :=
    integral_nonneg fun x => norm_nonneg _
  have hfinite : (∫⁻ x : InfinitePlace F → ℂ, ENNReal.ofReal ‖f x‖) < ⊤ := by
    rw [hlin]
    simp_rw [hnormint]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum]
    exact ENNReal.ofReal_lt_top
  have hintglobal : Integrable f :=
    ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_norm f).2 hfinite⟩
  refine ⟨hintglobal, ?_⟩
  calc
    _ = ∑' t : L, ∫ x in B, f ((t : InfinitePlace F → ℂ) + x) :=
      hBd.integral_eq_tsum'' f hintglobal
    _ = ∑' ξ : H, ∫ x in B, f ((e ξ : InfinitePlace F → ℂ) + x) :=
      (e.toEquiv.tsum_eq _).symm
    _ = _ := by simp only [heval, H]

/-- Rational big-cell periods unfold to globally integrable archimedean summands. -/
theorem eisenstein_bigCell_unfold_periods
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hfix : ∀ α ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P α * g)) = scalarOf P G Fs.f Fs.fC h)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBK : B ⊆ K)
    (hBd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) B volume)
    (δ : Fˣ ⧸ G.Δ) :
    (∀ η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
      Integrable (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
          nInf P x * g))) ∧
    Summable (fun η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup =>
      ∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
          nInf P x * g)‖) ∧
    (∑' ξ : F, ∫ x in B, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * nInf P x * g)) =
      ∑' η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
        ∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
          (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
            nInf P x * g) := by
  classical
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let J := (𝔞 : Submodule (𝓞 F) F).toAddSubgroup
  let Q := F ⧸ J
  let f (ξ : F) (x : InfinitePlace F → ℂ) : ℂ := scalarOf P G Fs.f Fs.fC
    (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * nInf P x * g)
  obtain ⟨e, _, hbig⟩ := rational_bruhat_coset_equiv P G
  obtain ⟨_, habs, _⟩ := eisenstein_integral_tsum_on_compact P G hs Fs g K hK B hB hBK
  have hrep (ξ : F) (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out (e (Sum.inr (δ, ξ)))) * nInf P x * g) = f ξ x := by
    let γ := diagGL (Quotient.out δ) * weylGL * upperGL ξ
    have hb : γ * (Quotient.out (e (Sum.inr (δ, ξ))))⁻¹ ∈ Bstar G :=
      QuotientGroup.rightRel_apply.mp
        (Quotient.exact ((Quotient.out_eq (e (Sum.inr (δ, ξ)))).trans (hbig δ ξ)))
    dsimp only [f]
    simpa only [γ, map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (γ * (Quotient.out (e (Sum.inr (δ, ξ))))⁻¹) hb
        (P.tc.rat (Quotient.out (e (Sum.inr (δ, ξ)))) * (nInf P x * g))).symm
  have hrepNorm (ξ : F) :
      (∫ x in B, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out (e (Sum.inr (δ, ξ)))) * nInf P x * g)‖) =
        ∫ x in B, ‖f ξ x‖ := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact congrArg norm (hrep ξ x)
  have hinj : Function.Injective (fun ξ : F => e (Sum.inr (δ, ξ))) :=
    e.injective.comp (Sum.inr_injective.comp (Prod.mk_right_injective δ))
  have hnormSeries : Summable (fun ξ : F => ∫ x in B, ‖f ξ x‖) :=
    (habs.comp_injective hinj).congr hrepNorm
  have hcomplexSeries : Summable (fun ξ : F => ∫ x in B, f ξ x) :=
    hnormSeries.of_norm_bounded fun ξ => norm_integral_le_integral_norm _
  have hcont (ξ : F) : Continuous (f ξ) :=
    scalarOf_unipotent_continuous P G Fs g
      (diagGL (Quotient.out δ) * weylGL * upperGL ξ)
  have hupper (u v : F) : upperGL (u + v) = upperGL u * upperGL v := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperGL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hperiod (ξ : F) (α : J) (x : InfinitePlace F → ℂ) :
      f (ξ + (α : F)) x = f ξ (infEmbA (α : F) + x) := by
    dsimp only [f]
    have hm : diagGL (Quotient.out δ) * weylGL * upperGL (ξ + (α : F)) =
        (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * upperGL (α : F) := by
      simp only [hupper, mul_assoc]
    rw [hm]
    exact scalarOf_rational_period_translate P G Fs g
      (diagGL (Quotient.out δ) * weylGL * upperGL ξ) (α : F) x
      (hfix (α : F) α.property)
  let r (p : Q × J) : F := Quotient.out p.1 + (p.2 : F)
  have hrclass (p : Q × J) : (QuotientAddGroup.mk (r p) : Q) = p.1 := by
    calc
      _ = QuotientAddGroup.mk (Quotient.out p.1) := by
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        have hd : r p - Quotient.out p.1 = (p.2 : F) := by dsimp only [r]; abel
        simpa only [hd] using p.2.property
      _ = p.1 := QuotientAddGroup.out_eq' p.1
  have hrbij : Function.Bijective r := by
    constructor
    · intro p q hpq
      have hq : p.1 = q.1 := by
        calc
          p.1 = (QuotientAddGroup.mk (r p) : Q) := (hrclass p).symm
          _ = QuotientAddGroup.mk (r q) := congrArg (fun z : F => (QuotientAddGroup.mk z : Q)) hpq
          _ = q.1 := hrclass q
      have ha : p.2 = q.2 := by
        apply Subtype.ext
        dsimp only [r] at hpq
        rw [hq] at hpq
        exact add_left_cancel hpq
      exact Prod.ext hq ha
    · intro ξ
      let η : Q := QuotientAddGroup.mk ξ
      have ha : ξ - Quotient.out η ∈ J :=
        QuotientAddGroup.eq_iff_sub_mem.mp ((QuotientAddGroup.out_eq' η).symm)
      refine ⟨(η, ⟨ξ - Quotient.out η, ha⟩), ?_⟩
      change Quotient.out η + (ξ - Quotient.out η) = ξ
      abel
  let ep : F ≃ Q × J := (Equiv.ofBijective r hrbij).symm
  have hep (p : Q × J) : ep.symm p = Quotient.out p.1 + (p.2 : F) := rfl
  have hpairNorm : Summable (fun p : Q × J =>
      ∫ x in B, ‖f (Quotient.out p.1 + (p.2 : F)) x‖) := by
    simpa only [Function.comp_def, hep] using hnormSeries.comp_injective ep.symm.injective
  have hshiftNorm (p : Q × J) :
      (∫ x in B, ‖f (Quotient.out p.1 + (p.2 : F)) x‖) =
        ∫ x in B, ‖f (Quotient.out p.1) (infEmbA (p.2 : F) + x)‖ := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact congrArg norm (hperiod (Quotient.out p.1) p.2 x)
  have htranslatedNorm : Summable (fun p : Q × J =>
      ∫ x in B, ‖f (Quotient.out p.1) (infEmbA (p.2 : F) + x)‖) :=
    hpairNorm.congr hshiftNorm
  have ht (η : Q) : Integrable (f (Quotient.out η)) ∧
      (∫ x : InfinitePlace F → ℂ, f (Quotient.out η) x) =
        ∑' α : J, ∫ x in B, f (Quotient.out η) (infEmbA (α : F) + x) :=
    ideal_domain_integral_tiling 𝔞 K hK B hB hBK hBd
      (f (Quotient.out η)) (hcont (Quotient.out η)) (htranslatedNorm.prod_factor η)
  let L := J.map (infEmbA (F := F)).toAddMonoidHom
  let ea : J ≃+ L := J.equivMapOfInjective (infEmbA (F := F)).toAddMonoidHom
    (infEmbA (F := F)).injective
  let : Countable L := ea.symm.injective.countable
  have heval (α : J) : (ea α : InfinitePlace F → ℂ) = infEmbA (α : F) := rfl
  have hnormTiling (η : Q) :
      (∫ x : InfinitePlace F → ℂ, ‖f (Quotient.out η) x‖) =
        ∑' α : J, ∫ x in B, ‖f (Quotient.out η) (infEmbA (α : F) + x)‖ := by
    calc
      _ = ∑' t : L, ∫ x in B, ‖f (Quotient.out η) ((t : InfinitePlace F → ℂ) + x)‖ :=
        hBd.integral_eq_tsum'' (fun x => ‖f (Quotient.out η) x‖) (ht η).1.norm
      _ = ∑' α : J, ∫ x in B, ‖f (Quotient.out η) ((ea α : InfinitePlace F → ℂ) + x)‖ :=
        (ea.toEquiv.tsum_eq _).symm
      _ = _ := by simp only [heval]
  have hglobalNorm : Summable (fun η : Q =>
      ∫ x : InfinitePlace F → ℂ, ‖f (Quotient.out η) x‖) :=
    htranslatedNorm.prod.congr (fun η => (hnormTiling η).symm)
  have hpairComplex : Summable (fun p : Q × J => ∫ x in B, f (ep.symm p) x) :=
    hcomplexSeries.comp_injective ep.symm.injective
  refine ⟨?_, ?_, ?_⟩
  · intro η
    exact (ht η).1
  · simpa only [f, Q, J] using hglobalNorm
  · change (∑' ξ : F, ∫ x in B, f ξ x) =
      ∑' η : Q, ∫ x : InfinitePlace F → ℂ, f (Quotient.out η) x
    calc
      _ = ∑' p : Q × J, ∫ x in B, f (ep.symm p) x := (ep.symm.tsum_eq _).symm
      _ = ∑' η : Q, ∑' α : J, ∫ x in B, f (ep.symm (η, α)) x := hpairComplex.tsum_prod
      _ = _ := by
        apply tsum_congr
        intro η
        calc
          _ = ∑' α : J, ∫ x in B, f (Quotient.out η) (infEmbA (α : F) + x) := by
            apply tsum_congr
            intro α
            rw [hep]
            apply integral_congr_ae
            filter_upwards [] with x
            exact hperiod (Quotient.out η) α x
          _ = _ := (ht η).2.symm

/-- Rational unipotent representatives can be shifted to finite coordinates under global integration. -/
theorem scalarOf_finitePeriod_arch_integral
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G)
    (γ : GL (Fin 2) F) (ξ : F)
    (hint : Integrable (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL ξ) * nInf P x * g))) :
    Integrable (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat γ * nFin P ξ * nInf P x * g)) ∧
    (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL ξ) * nInf P x * g)) =
      (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
        (P.tc.rat γ * nFin P ξ * nInf P x * g)) ∧
    (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL ξ) * nInf P x * g)‖) =
      ∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat γ * nFin P ξ * nInf P x * g)‖ := by
  have hni (y z : InfinitePlace F → ℂ) : nInf P (y + z) = nInf P y * nInf P z := by
    dsimp only [nInf]
    have hp : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y + z) =
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y) +
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), z) := by simp
    rw [hp, ofAdd_add, map_mul]
  have hfactor (x : InfinitePlace F → ℂ) :
      P.tc.rat γ * nFin P ξ * nInf P x * g =
        P.tc.rat (γ * upperGL ξ) * nInf P (-infEmbA ξ + x) * g := by
    dsimp only [nFin]
    calc
      _ = (P.tc.rat γ * P.tc.rat (upperGL ξ)) *
          (nInf P (-infEmbA ξ) * nInf P x) * g := by group
      _ = (P.tc.rat γ * P.tc.rat (upperGL ξ)) *
          nInf P (-infEmbA ξ + x) * g := by rw [← hni]
      _ = _ := by rw [map_mul]
  have heq (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat γ * nFin P ξ * nInf P x * g) =
        scalarOf P G Fs.f Fs.fC
          (P.tc.rat (γ * upperGL ξ) * nInf P (-infEmbA ξ + x) * g) := by
    rw [hfactor]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [heq] using hint.comp_add_left (-infEmbA ξ)
  · simp_rw [heq]
    exact (integral_add_left_eq_self
      (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
        (P.tc.rat (γ * upperGL ξ) * nInf P x * g)) (-infEmbA ξ)).symm
  · simp_rw [heq]
    exact (integral_add_left_eq_self
      (fun x : InfinitePlace F → ℂ => ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (γ * upperGL ξ) * nInf P x * g)‖) (-infEmbA ξ)).symm

/-- The fractional-ideal norm is the finite product of residue-field norms to valuation counts. -/
theorem fractionalIdeal_absNorm_finprod
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0) :
    (FractionalIdeal.absNorm 𝔞 : ℝ) =
      ∏ᶠ v : FinPlace F, (qv v) ^ (FractionalIdeal.count F v 𝔞) := by
  classical
  let FI := FractionalIdeal (nonZeroDivisors (𝓞 F)) F
  let d (v : FinPlace F) : ℤ := FractionalIdeal.count F v 𝔞
  let fac (v : FinPlace F) : FI := (v.asIdeal : FI) ^ d v
  let normH : FI →*₀ ℝ :=
    (Rat.castHom ℝ).toMonoidWithZeroHom.comp FractionalIdeal.absNorm
  have hd : (Function.support d).Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors 𝔞)
  have hfinite : Function.HasFiniteMulSupport fac := by
    apply hd.subset
    intro v hv
    change d v ≠ 0
    intro hz
    exact hv (by simp only [fac, hz, zpow_zero])
  have hfac : (∏ᶠ v : FinPlace F, fac v) = 𝔞 :=
    FractionalIdeal.finprod_heightOneSpectrum_factorization' F h𝔞
  calc
    _ = normH (∏ᶠ v : FinPlace F, fac v) := by rw [hfac]; rfl
    _ = ∏ᶠ v : FinPlace F, normH (fac v) := normH.toMonoidHom.map_finprod hfinite
    _ = _ := by
      apply finprod_congr
      intro v
      change normH ((v.asIdeal : FI) ^ d v) = (qv v) ^ d v
      rw [map_zpow₀]
      congr 1
      change (FractionalIdeal.absNorm
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ℝ) = qv v
      rw [FractionalIdeal.coeIdeal_absNorm (K := F)]
      simp [qv]

/-- At a fixed restricted-product lift, integration over the complex coordinates
factors, for both the scalar section and its absolute majorant. -/
theorem scalarOf_arch_integral_product
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (r : P.RP) (γ : GL (Fin 2) F) :
    (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
      (P.tc.rat γ * nInf P x * P.q r)) =
      (∏ᶠ v, G.lam v (Fs.f v (P.compF v (P.ratRP γ * r)))) *
        ∏ w, ∫ z : ℂ, Fs.fC w
          (P.compC w (P.ratRP γ) * nC z * P.compC w r) ∧
    (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
      (P.tc.rat γ * nInf P x * P.q r)‖) =
      ‖∏ᶠ v, G.lam v (Fs.f v (P.compF v (P.ratRP γ * r)))‖ *
        ∏ w, ∫ z : ℂ, ‖Fs.fC w
          (P.compC w (P.ratRP γ) * nC z * P.compC w r)‖ := by
  classical
  choose rn hqn hfn hcn using fun x : InfinitePlace F → ℂ =>
    P.nS_components ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  have hfn1 (x : InfinitePlace F → ℂ) (v : FinPlace F) : P.compF v (rn x) = 1 := by
    simpa using hfn x v
  let R (x : InfinitePlace F → ℂ) : P.RP := P.ratRP γ * rn x * r
  let cf : ℂ := ∏ᶠ v, G.lam v (Fs.f v (P.compF v (P.ratRP γ * r)))
  let fc (w : InfinitePlace F) (z : ℂ) : ℂ :=
    Fs.fC w (P.compC w (P.ratRP γ) * nC z * P.compC w r)
  have hq (x : InfinitePlace F → ℂ) :
      P.q (R x) = P.tc.rat γ * nInf P x * P.q r := by
    simp only [R, map_mul, P.q_ratRP, hqn, nInf]
  have hcompF (x : InfinitePlace F → ℂ) (v : FinPlace F) :
      P.compF v (R x) = P.compF v (P.ratRP γ * r) := by
    simp only [R, map_mul, hfn1, mul_one]
  have hcompC (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      P.compC w (R x) = P.compC w (P.ratRP γ) * nC (x w) * P.compC w r := by
    simp only [R, map_mul, hcn, nC]
  have hformula (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat γ * nInf P x * P.q r) =
        cf * ∏ w, fc w (x w) := by
    rw [← hq, (scalarOf_q P G Fs (R x)).2]
    simp only [cf, fc, hcompF, hcompC]
  constructor
  · change (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
      (P.tc.rat γ * nInf P x * P.q r)) = cf * ∏ w, ∫ z : ℂ, fc w z
    calc
      _ = ∫ x : InfinitePlace F → ℂ, cf * ∏ w, fc w (x w) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hformula x
      _ = cf * ∫ x : InfinitePlace F → ℂ, ∏ w, fc w (x w) := integral_const_mul _ _
      _ = _ := by rw [integral_fintype_prod_volume_eq_prod]
  · change (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
      (P.tc.rat γ * nInf P x * P.q r)‖) = ‖cf‖ * ∏ w, ∫ z : ℂ, ‖fc w z‖
    calc
      _ = ∫ x : InfinitePlace F → ℂ, ‖cf‖ * ∏ w, ‖fc w (x w)‖ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hformula, norm_mul, norm_prod]
      _ = ‖cf‖ * ∫ x : InfinitePlace F → ℂ, ∏ w, ‖fc w (x w)‖ := integral_const_mul _ _
      _ = _ := by
        rw [integral_fintype_prod_volume_eq_prod (fun w (z : ℂ) => ‖fc w z‖)]

/-- A rational finite unipotent has the expected finite components and
trivial complex components in a restricted-product lift. -/
theorem nFin_components
    (P : CoverPackage D S H A) (ξ : F) :
    ∃ r : P.RP, P.q r = nFin P ξ ∧
      (∀ v : FinPlace F, P.compF v r =
        (P.loc v).n (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F) ξ))) ∧
      ∀ w : InfinitePlace F, P.compC w r = 1 := by
  classical
  obtain ⟨t, hqt, hft, hct⟩ := P.nS_components
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), -infEmbA ξ)
  have hft1 (v : FinPlace F) : P.compF v t = 1 := by
    simpa using hft v
  have hupper {K : Type} [Field K] (ι : F →+* K) :
      Matrix.GeneralLinearGroup.map ι (upperGL ξ) = upperM K (ι ξ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.map, upperGL, upperM]
  have hcancel (z : ℂ) : upperM ℂ z * upperM ℂ (-z) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨P.ratRP (upperGL ξ) * t, ?_, ?_, ?_⟩
  · simp only [map_mul, P.q_ratRP, hqt, nFin, nInf]
  · intro v
    rw [map_mul, hft1, mul_one, P.compF_ratRP, hupper, ← (P.loc v).sec_n]
  · intro w
    rw [map_mul, P.compC_ratRP, hupper, hct]
    change (QuotientGroup.mk (upperM ℂ (w.embedding ξ)) : PGL2 ℂ) *
      QuotientGroup.mk (upperM ℂ (-w.embedding ξ)) = 1
    rw [← QuotientGroup.mk_mul, hcancel, QuotientGroup.mk_one]

/-- Rational ideal periods extend to all compatible finite-adelic ideal translations. -/
theorem scalarOf_ideal_local_periods
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (r : P.RP)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC
        (h * ((P.q r)⁻¹ * nFin P ξ * P.q r)) = scalarOf P G Fs.f Fs.fC h)
    (x : ∀ v : FinPlace F, v.adicCompletion F)
    (hx : ∀ v : FinPlace F, x v ∈ idealLocalPeriods 𝔞 v)
    (t : P.RP)
    (htF : ∀ v : FinPlace F, P.compF v t = (P.loc v).n (Multiplicative.ofAdd (x v)))
    (htC : ∀ w : InfinitePlace F, P.compC w t = 1)
    (z : P.RP) :
    scalarOf P G Fs.f Fs.fC (P.q (z * t * r)) =
      scalarOf P G Fs.f Fs.fC (P.q (z * r)) := by
  classical
  have hball (v : FinPlace F) (m : ℕ) (y : v.adicCompletion F)
      (hy : absFin v y ≤ (qv v) ^ (-(m : ℤ))) : y ∈ ball v m := by
    let K := v.adicCompletion F
    have hπval : Valued.v (unifLoc v : K) = WithZero.exp (-1 : ℤ) := by
      have hcoe : (unifLoc v : K) = algebraMap F K (unif v) := by
        simp [unifLoc, toLoc, K]
      rw [hcoe]
      change Valued.v ((unif v : F) : v.adicCompletion F) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
    have hπnorm : absFin v (unifLoc v : K) = (qv v)⁻¹ := by
      rw [absFin_eq_norm, FinitePlace.norm_def, hπval]
      rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) (by simp)]
      rw [WithZero.toAdd_unzero_eq_log (by simp)]
      simp [qv]
    let ρ : Kˣ := unifLoc v ^ (m : ℤ)
    have hρnorm : absFin v (ρ : K) = (qv v) ^ (-(m : ℤ)) := by
      dsimp only [ρ]
      rw [absFin_eq_norm, Units.val_zpow_eq_zpow_val, norm_zpow,
        ← absFin_eq_norm v (unifLoc v : K), hπnorm, inv_zpow, zpow_neg]
    have hρval : Valued.v (ρ : K) = WithZero.exp (-(m : ℤ)) := by
      dsimp only [ρ]
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπval]
      simp
    change Valued.v y ≤ WithZero.exp (-(m : ℤ))
    rw [← hρval]
    apply Valued.toNormedField.norm_le_iff.mp
    simpa only [← absFin_eq_norm, hρnorm] using hy
  choose m hm hright using fun v : FinPlace F =>
    ((Fs.f_sec v).rtr (P.compF v r)).2.2
  let W : Finset (FinPlace F) := Fs.T0 ∪ (P.comp_restricted r).toFinset
  let e (v : FinPlace F) : ℤ := if v ∈ W then (m v : ℤ) else 0
  have he : (Function.support e).Finite := by
    apply W.finite_toSet.subset
    intro v hv
    by_contra hvW
    change v ∉ W at hvW
    exact hv (by simp only [e, ite_eq_right hvW])
  obtain ⟨ξ, hξmem, happ⟩ := ideal_period_additive_approximation 𝔞 h𝔞 x hx e he
  obtain ⟨tξ, hqξ, hFξ, hCξ⟩ := nFin_components P ξ
  let ε (v : FinPlace F) : v.adicCompletion F :=
    x v - algebraMap F (v.adicCompletion F) ξ
  have hn (v : FinPlace F) :
      (P.loc v).n (Multiplicative.ofAdd (x v)) =
        (P.loc v).n (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F) ξ)) *
          (P.loc v).n (Multiplicative.ofAdd (ε v)) := by
    have hsum : algebraMap F (v.adicCompletion F) ξ + ε v = x v := by
      dsimp only [ε]
      abel
    rw [← map_mul, ← ofAdd_add, hsum]
  have hlocal (v : FinPlace F) (h : (P.loc v).L) :
      Fs.f v ((h * (P.loc v).n (Multiplicative.ofAdd (ε v))) * P.compF v r) =
        Fs.f v (h * P.compF v r) := by
    by_cases hvW : v ∈ W
    · have hb : ε v ∈ ball v (m v) := hball v (m v) (ε v) (by
        simpa only [e, ite_eq_left hvW] using happ v)
      simpa only [rtr] using hright v h ((P.loc v).n (Multiplicative.ofAdd (ε v)))
        ((P.loc v).n_Kc (m v) (hm v) (ε v) hb)
    · have hvT : v ∉ Fs.T0 := fun hv => hvW (Finset.mem_union_left _ hv)
      have hvS : v ∉ S.Sf := fun hv => hvT (Fs.sub hv)
      have hg : P.compF v r ∈ (P.tame v hvS).Kmax := by
        by_contra hnot
        apply hvW
        exact Finset.mem_union_right _ ((P.comp_restricted r).mem_toFinset.mpr ⟨hvS, hnot⟩)
      have hεint : ε v ∈ v.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers,
          ← Valued.toNormedField.norm_le_one_iff]
        simpa only [e, ite_eq_right hvW, neg_zero, zpow_zero, absFin_eq_norm] using happ v
      have hk : (P.compF v r)⁻¹ * (P.loc v).n (Multiplicative.ofAdd (ε v)) *
          P.compF v r ∈ (P.tame v hvS).Kmax :=
        (P.tame v hvS).Kmax.mul_mem
          ((P.tame v hvS).Kmax.mul_mem ((P.tame v hvS).Kmax.inv_mem hg)
            ((P.tame v hvS).n_mem (ε v) hεint)) hg
      have hf := (Fs.f_sph v hvT).2 (h * P.compF v r)
        ((P.compF v r)⁻¹ * (P.loc v).n (Multiplicative.ofAdd (ε v)) * P.compF v r) hk
      rw [show (h * P.compF v r) *
          ((P.compF v r)⁻¹ * (P.loc v).n (Multiplicative.ofAdd (ε v)) * P.compF v r) =
          (h * (P.loc v).n (Multiplicative.ofAdd (ε v))) * P.compF v r by group] at hf
      exact hf
  have hF (v : FinPlace F) :
      Fs.f v (P.compF v (z * t * r)) = Fs.f v (P.compF v (z * tξ * r)) := by
    simp only [map_mul, htF, hFξ, hn]
    simpa only [mul_assoc] using hlocal v
      (P.compF v z * (P.loc v).n (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F) ξ)))
  calc
    _ = scalarOf P G Fs.f Fs.fC (P.q (z * tξ * r)) := by
      apply scalarOf_lift_components Fs (z * t * r) (z * tξ * r)
      · intro v
        exact congrArg (G.lam v) (hF v)
      · intro w
        simp only [map_mul, htC, hCξ, mul_one]
    _ = _ := by
      have harg : P.q (z * tξ * r) =
          (P.q z * P.q r) * ((P.q r)⁻¹ * nFin P ξ * P.q r) := by
        rw [map_mul, map_mul, hqξ]
        group
      rw [harg, map_mul]
      exact hfix ξ hξmem (P.q z * P.q r)

/-- A nonzero global scalar tensor transfers its ideal periods to each local scalar factor. -/
theorem local_scalar_ideal_periods_of_nonzero
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (r : P.RP)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC
        (h * ((P.q r)⁻¹ * nFin P ξ * P.q r)) = scalarOf P G Fs.f Fs.fC h)
    (hΦ : ∃ g : P.tc.G, scalarOf P G Fs.f Fs.fC g ≠ 0)
    (v : FinPlace F) (a : (P.loc v).L)
    (y : v.adicCompletion F) (hy : y ∈ idealLocalPeriods 𝔞 v) :
    G.lam v (Fs.f v (a * (P.loc v).n (Multiplicative.ofAdd y) * P.compF v r)) =
      G.lam v (Fs.f v (a * P.compF v r)) := by
  classical
  obtain ⟨g0, hg0⟩ := hΦ
  obtain ⟨b, hqb⟩ := P.q_surj g0
  let β (u : FinPlace F) : ℂ := G.lam u (Fs.f u (P.compF u b))
  have hβ : (Function.mulSupport β).Finite := (scalarOf_q P G Fs b).1
  let U : Finset (FinPlace F) := hβ.toFinset.erase v
  let C : ℂ := ∏ w, Fs.fC w (P.compC w b)
  let B : ℂ := (∏ u ∈ U, β u) * C
  have hprod (f : FinPlace F → ℂ) (hf : ∀ u, u ≠ v → f u = β u) :
      (∏ᶠ u, f u) = f v * ∏ u ∈ U, β u := by
    have hs : Function.mulSupport f ⊆ ((insert v U : Finset (FinPlace F)) : Set (FinPlace F)) := by
      intro u hu
      by_cases huv : u = v
      · subst u
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_erase.mpr
        refine ⟨huv, hβ.mem_toFinset.mpr ?_⟩
        change β u ≠ 1
        rw [← hf u huv]
        exact hu
    rw [finprod_eq_prod_of_mulSupport_subset f hs,
      Finset.prod_insert (Finset.notMem_erase v hβ.toFinset)]
    congr 1
    apply Finset.prod_congr rfl
    intro u hu
    exact hf u (Finset.mem_erase.mp hu).1
  have hbaseline : scalarOf P G Fs.f Fs.fC (P.q b) = β v * B := by
    rw [(scalarOf_q P G Fs b).2]
    change (∏ᶠ u, β u) * C = β v * B
    rw [hprod β (fun _ _ => rfl)]
    exact mul_assoc _ _ _
  have hB : B ≠ 0 := by
    apply (mul_ne_zero_iff.mp (show β v * B ≠ 0 from ?_)).2
    rw [← hbaseline, hqb]
    exact hg0
  let Z (k : (P.loc v).L) : P.RP :=
    (b * r⁻¹) * P.incl v ((P.compF v (b * r⁻¹))⁻¹ * k)
  have hZF (k : (P.loc v).L) : P.compF v (Z k * r) = k * P.compF v r := by
    simp only [Z, map_mul, P.incl_compF, map_inv]
    group
  have hZFother (k : (P.loc v).L) (u : FinPlace F) (hu : u ≠ v) :
      P.compF u (Z k * r) = P.compF u b := by
    simp only [Z, map_mul, P.incl_compF_other v u hu.symm, map_inv, mul_one]
    group
  have hZC (k : (P.loc v).L) (w : InfinitePlace F) :
      P.compC w (Z k * r) = P.compC w b := by
    simp only [Z, map_mul, P.incl_compC, map_inv, mul_one]
    group
  have heval (k : (P.loc v).L) :
      scalarOf P G Fs.f Fs.fC (P.q (Z k * r)) =
        G.lam v (Fs.f v (k * P.compF v r)) * B := by
    rw [(scalarOf_q P G Fs (Z k * r)).2]
    rw [hprod (fun u => G.lam u (Fs.f u (P.compF u (Z k * r)))) (by
      intro u hu
      rw [hZFother k u hu]), hZF]
    have harch : (∏ w, Fs.fC w (P.compC w (Z k * r))) = C := by
      dsimp only [C]
      apply Finset.prod_congr rfl
      intro w hw
      rw [hZC]
    rw [harch]
    exact mul_assoc _ _ _
  let x : ∀ u : FinPlace F, u.adicCompletion F := Pi.single v y
  have hx : ∀ u : FinPlace F, x u ∈ idealLocalPeriods 𝔞 u := by
    intro u
    by_cases hu : u = v
    · subst u
      simpa only [x, Pi.single_eq_same] using hy
    · have hx0 : x u = 0 := by simp [x, hu]
      rw [hx0]
      exact (idealLocalPeriods 𝔞 u).zero_mem
  let t : P.RP := P.incl v ((P.loc v).n (Multiplicative.ofAdd y))
  have htF (u : FinPlace F) :
      P.compF u t = (P.loc u).n (Multiplicative.ofAdd (x u)) := by
    by_cases hu : u = v
    · subst u
      simp only [t, P.incl_compF, x, Pi.single_eq_same]
    · dsimp only [t]
      rw [P.incl_compF_other v u (Ne.symm hu)]
      simp [x, hu]
  have htC (w : InfinitePlace F) : P.compC w t = 1 :=
    P.incl_compC v _ w
  have hZmul (k l : (P.loc v).L) : Z k * P.incl v l = Z (k * l) := by
    dsimp only [Z]
    simp only [map_mul, mul_assoc]
  have hper := scalarOf_ideal_local_periods P G Fs r 𝔞 h𝔞 hfix x hx t htF htC (Z a)
  dsimp only [t] at hper
  rw [hZmul, heval, heval] at hper
  exact mul_right_cancel₀ hB hper

/-- An identically zero scalar tensor has a zero finite exceptional or complex factor. -/
theorem scalarOf_zero_has_zero_factor
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s)
    (hzero : ∀ g : P.tc.G, scalarOf P G Fs.f Fs.fC g = 0) :
    (∃ v : FinPlace F, v ∈ Fs.T0 ∧
      ∀ k : (P.loc v).L, G.lam v (Fs.f v k) = 0) ∨
    (∃ w : InfinitePlace F, ∀ k : PGL2 ℂ, Fs.fC w k = 0) := by
  classical
  by_contra hnone
  have hfin : ∀ v : Fs.T0, ∃ a : (P.loc v.1).L,
      G.lam v.1 (Fs.f v.1 a) ≠ 0 := by
    intro v
    by_contra hn
    push_neg at hn
    exact hnone (Or.inl ⟨v.1, v.property, hn⟩)
  have harch : ∀ w : InfinitePlace F, ∃ k : PGL2 ℂ, Fs.fC w k ≠ 0 := by
    intro w
    by_contra hn
    push_neg at hn
    exact hnone (Or.inr ⟨w, hn⟩)
  choose a ha using hfin
  choose k hk using harch
  let lf (v : FinPlace F) : (P.loc v).L :=
    if hv : v ∈ Fs.T0 then a ⟨v, hv⟩ else 1
  have hrestricted :
      Set.Finite {v : FinPlace F | ∃ hv : v ∉ S.Sf, lf v ∉ (P.tame v hv).Kmax} := by
    apply Fs.T0.finite_toSet.subset
    intro v hv
    by_contra hvT
    change v ∉ Fs.T0 at hvT
    obtain ⟨hvS, hnot⟩ := hv
    apply hnot
    simpa only [lf, dif_neg hvT] using (P.tame v hvS).Kmax.one_mem
  obtain ⟨r, hrF, hrC⟩ := P.comp_surj lf k hrestricted
  let f (v : FinPlace F) : ℂ := G.lam v (Fs.f v (P.compF v r))
  have hout (v : FinPlace F) (hv : v ∉ Fs.T0) : f v = 1 := by
    dsimp only [f]
    rw [hrF]
    simp only [lf, dif_neg hv]
    rw [(Fs.f_sph v hv).1]
    simpa using G.lam_tame v (fun h => hv (Fs.sub h)) 0
  have hprod : (∏ᶠ v, f v) = ∏ v ∈ Fs.T0, f v :=
    finprod_eq_prod_of_mulSupport_subset f (Function.mulSupport_subset_iff'.2 hout)
  have hlocalNe : (∏ v ∈ Fs.T0, f v) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    dsimp only [f]
    rw [hrF]
    simp only [lf, dif_pos hv]
    exact ha ⟨v, hv⟩
  have harchNe : (∏ w, Fs.fC w (P.compC w r)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro w hw
    rw [hrC]
    exact hk w
  have hne : scalarOf P G Fs.f Fs.fC (P.q r) ≠ 0 := by
    rw [(scalarOf_q P G Fs r).2]
    change (∏ᶠ v, f v) * (∏ w, Fs.fC w (P.compC w r)) ≠ 0
    rw [hprod]
    exact mul_ne_zero hlocalNe harchNe
  exact hne (hzero (P.q r))

set_option backward.isDefEq.respectTransparency false in
/-- The intertwined scalar has finite local support and the same formula at any RP lift. -/
theorem scalarM_q
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (Fs : GlobalSection P G s) (r : P.RP) :
    let fM : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V := fun v =>
      if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
      else sphWeyl P G v (fun h => hv (Fs.sub h)) s
    (Function.mulSupport fun v => G.lam v (fM v (P.compF v r))).Finite ∧
    scalarM P G μ Fs (P.q r) =
      (κF F)⁻¹ * cprod Fs.T0 s *
        ((∏ᶠ v, G.lam v (fM v (P.compF v r))) *
          ∏ w, intertwineC (Fs.fC w) (P.compC w r)) := by
  classical
  let fM : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V := fun v =>
    if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
    else sphWeyl P G v (fun h => hv (Fs.sub h)) s
  change (Function.mulSupport fun v => G.lam v (fM v (P.compF v r))).Finite ∧
    scalarM P G μ Fs (P.q r) =
      (κF F)⁻¹ * cprod Fs.T0 s *
        ((∏ᶠ v, G.lam v (fM v (P.compF v r))) *
          ∏ w, intertwineC (Fs.fC w) (P.compC w r))
  have hgen (v : FinPlace F) (ζ : rootsOfUnity 3 ℂ) (a : (P.loc v).L) :
      fM v ((P.loc v).z ζ * a) = ((ζ : ℂˣ) : ℂ) • fM v a := by
    dsimp only [fM]
    by_cases hv : v ∈ Fs.T0
    · simp only [dite_eq_left hv]
      simpa only [TorusRep.weyl] using
        (intertwine_isSection (P.loc v) (G.T v) (μ v) s hs (Fs.f v)
          (Fs.f_sec v)).2.2.1 ζ a
    · simp only [dite_eq_right hv]
      simpa only [sphWeyl, TorusRep.weyl] using
        ((spherical_section (P.loc v) (P.tame v (fun h => hv (Fs.sub h)))
          (G.T v).weyl (G.B v (fun h => hv (Fs.sub h))).weyl
          (fun h => hv (Fs.sub (S.over6 v h))) (-s)).choose_spec.1).2.1 ζ a
  have hfinite (a : P.RP) :
      (Function.mulSupport fun v => G.lam v (fM v (P.compF v a))).Finite := by
    apply Set.Finite.subset (Fs.T0.finite_toSet.union (P.comp_restricted a))
    intro v hv
    by_contra hvout
    have hvT : v ∉ Fs.T0 := fun h => hvout (Or.inl h)
    have hvS : v ∉ S.Sf := fun h => hvT (Fs.sub h)
    have hK : P.compF v a ∈ (P.tame v hvS).Kmax := by
      by_contra hK
      exact hvout (Or.inr ⟨hvS, hK⟩)
    have hf0 := (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl
      (G.B v hvS).weyl (fun h => hvS (S.over6 v h)) (-s)).choose_spec
    have hf : fM v (P.compF v a) = (G.B v hvS).e 0 := by
      dsimp only [fM]
      rw [dite_eq_right hvT]
      calc
        sphWeyl P G v hvS s (P.compF v a) =
            sphWeyl P G v hvS s (1 * P.compF v a) := by rw [one_mul]
        _ = sphWeyl P G v hvS s 1 := hf0.2.2.1 1 (P.compF v a) hK
        _ = (G.B v hvS).e 0 := by
          simpa only [sphWeyl, TorusRep.weyl, TameTorusBasis.weyl, neg_zero] using hf0.2.1
    have hlam : G.lam v (fM v (P.compF v a)) = 1 := by
      rw [hf]
      simpa using G.lam_tame v hvS 0
    exact hv hlam
  let y : P.RP := Function.surjInv P.q_surj (P.q r)
  have hq : P.q r = P.q y :=
    (Function.rightInverse_surjInv P.q_surj (P.q r)).symm
  obtain ⟨ζ, hζfin, hζprod, hcomp, hcompC⟩ := (P.q_eq r y).mp hq
  let α : FinPlace F → ℂ := fun v => G.lam v (fM v (P.compF v r))
  let β : FinPlace F → ℂ := fun v => G.lam v (fM v (P.compF v y))
  have hrel : α = fun v => ((ζ v : ℂˣ) : ℂ) * β v := by
    funext v
    dsimp only [α, β]
    rw [hcomp v, hgen v]
    simp
  let eval : rootsOfUnity 3 ℂ →* ℂ :=
    { toFun := fun z => ((z : ℂˣ) : ℂ)
      map_one' := rfl
      map_mul' := by intros; rfl }
  have hζscalarfin : (Function.mulSupport fun v => ((ζ v : ℂˣ) : ℂ)).Finite := by
    apply hζfin.subset
    intro v hv
    change ζ v ≠ 1
    intro h1
    exact hv (by change ((ζ v : ℂˣ) : ℂ) = 1; rw [h1]; rfl)
  have hζscalarprod : (∏ᶠ v, ((ζ v : ℂˣ) : ℂ)) = 1 := by
    calc
      _ = eval (∏ᶠ v, ζ v) := (eval.map_finprod hζfin).symm
      _ = 1 := by rw [hζprod, map_one]
  have hαprod : (∏ᶠ v, α v) = ∏ᶠ v, β v := by
    rw [hrel, finprod_mul_distrib hζscalarfin (hfinite y), hζscalarprod, one_mul]
  refine ⟨hfinite r, ?_⟩
  change (κF F)⁻¹ * cprod Fs.T0 s *
      ((∏ᶠ v, β v) * ∏ w, intertwineC (Fs.fC w) (P.compC w y)) =
    (κF F)⁻¹ * cprod Fs.T0 s *
      ((∏ᶠ v, α v) * ∏ w, intertwineC (Fs.fC w) (P.compC w r))
  rw [hαprod]
  congr 2
  apply Finset.prod_congr rfl
  intro w hw
  exact (congrArg (intertwineC (Fs.fC w)) (hcompC w)).symm

/-- Intertwining preserves an identically zero global scalar section. -/
theorem scalarM_eq_zero_of_scalarOf_eq_zero
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (Fs : GlobalSection P G s)
    (hzero : ∀ g : P.tc.G, scalarOf P G Fs.f Fs.fC g = 0)
    (g : P.tc.G) : scalarM P G μ Fs g = 0 := by
  classical
  obtain ⟨r, hr⟩ := P.q_surj g
  let fM : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V := fun v =>
    if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
    else sphWeyl P G v (fun h => hv (Fs.sub h)) s
  have hfinite : (Function.mulSupport fun v => G.lam v (fM v (P.compF v r))).Finite :=
    (scalarM_q P G μ hs Fs r).1
  rw [← hr, (scalarM_q P G μ hs Fs r).2]
  change (κF F)⁻¹ * cprod Fs.T0 s *
    ((∏ᶠ v, G.lam v (fM v (P.compF v r))) *
      ∏ w, intertwineC (Fs.fC w) (P.compC w r)) = 0
  rcases scalarOf_zero_has_zero_factor P G Fs hzero with ⟨v, hv, hlocal⟩ | ⟨w, harch⟩
  · have hM : G.lam v (intertwine (P.loc v) (μ v) (Fs.f v) (P.compF v r)) = 0 := by
      let lam : (G.T v).V →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (G.lam v)
      have hint := (intertwine_isSection (P.loc v) (G.T v) (μ v) s hs
        (Fs.f v) (Fs.f_sec v)).1 (P.compF v r)
      have hfun : (fun x : v.adicCompletion F =>
          lam (Fs.f v ((P.loc v).w * (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r))) =
          fun _ => (0 : ℂ) := by
        funext x
        exact hlocal _
      calc
        G.lam v (intertwine (P.loc v) (μ v) (Fs.f v) (P.compF v r)) =
            lam (∫ x, Fs.f v ((P.loc v).w * (P.loc v).n (Multiplicative.ofAdd x) *
              P.compF v r) ∂(μ v).μ) := rfl
        _ = ∫ x, lam (Fs.f v ((P.loc v).w * (P.loc v).n (Multiplicative.ofAdd x) *
              P.compF v r)) ∂(μ v).μ :=
          (ContinuousLinearMap.integral_comp_comm lam hint).symm
        _ = 0 := by rw [hfun, integral_zero]
    have hfactor : G.lam v (fM v (P.compF v r)) = 0 := by
      simpa only [fM, dite_eq_left hv] using hM
    rw [finprod_eq_zero _ v hfactor hfinite, zero_mul, mul_zero]
  · have hM : intertwineC (Fs.fC w) (P.compC w r) = 0 := by
      have hfun : (fun x : ℂ => Fs.fC w (wC * nC x * P.compC w r)) =
          fun _ => (0 : ℂ) := by
        funext x
        exact harch _
      rw [intertwineC, hfun, integral_zero]
    have hprod : (∏ w, intertwineC (Fs.fC w) (P.compC w r)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ w) hM
    rw [hprod, mul_zero, mul_zero]

/-- The constant-term formula when the original scalar section vanishes everywhere. -/
theorem eisenstein_constantTerm_of_zero
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (Fs : GlobalSection P G s)
    (hzero : ∀ g : P.tc.G, scalarOf P G Fs.f Fs.fC g = 0)
    (g : P.tc.G) (Pd : Set (InfinitePlace F → ℂ)) :
    torusCoeff P (eisenstein P G Fs) g Pd 0 =
      ∑' δ : Fˣ ⧸ G.Δ, (scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL (Quotient.out δ)) * g) +
        scalarM P G μ Fs (P.tc.rat (diagGL (Quotient.out δ)) * g)) := by
  have hE (h : P.tc.G) : eisenstein P G Fs h = 0 := by
    simp only [eisenstein, hzero, tsum_zero]
  have hM (h : P.tc.G) : scalarM P G μ Fs h = 0 :=
    scalarM_eq_zero_of_scalarOf_eq_zero P G μ hs Fs hzero h
  simp only [torusCoeff, hE, zero_mul, integral_zero, mul_zero, hzero, hM, add_zero,
    tsum_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Local Bruhat ideal-coset sums give the intertwine at the inverted torus element. -/
theorem local_bruhat_coset_hasSum
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (Fs : GlobalSection P G s) (r : P.RP)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC
        (h * ((P.q r)⁻¹ * nFin P ξ * P.q r)) = scalarOf P G Fs.f Fs.fC h)
    (hΦ : ∃ g : P.tc.G, scalarOf P G Fs.f Fs.fC g ≠ 0)
    (v : FinPlace F) (u : (v.adicCompletion F)ˣ) :
    let H : v.adicCompletion F → ℂ := fun x =>
      G.lam v (Fs.f v ((P.loc v).a u * (P.loc v).w *
        (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r))
    HasSum
      (fun η : (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v =>
        ((qv v) ^ (-FractionalIdeal.count F v 𝔞) : ℝ) • H (Quotient.out η))
      ((absFin v u : ℂ) * G.lam v
        (intertwine (P.loc v) (μ v) (Fs.f v) ((P.loc v).a u⁻¹ * P.compF v r))) ∧
    HasSum
      (fun η : (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v =>
        (qv v) ^ (-FractionalIdeal.count F v 𝔞) * ‖H (Quotient.out η)‖)
      (∫ x, ‖H x‖ ∂(μ v).μ) := by
  classical
  let Hfn : v.adicCompletion F → ℂ := fun x =>
    G.lam v (Fs.f v ((P.loc v).a u * (P.loc v).w *
      (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r))
  change HasSum
      (fun η : (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v =>
        ((qv v) ^ (-FractionalIdeal.count F v 𝔞) : ℝ) • Hfn (Quotient.out η))
      ((absFin v u : ℂ) * G.lam v
        (intertwine (P.loc v) (μ v) (Fs.f v) ((P.loc v).a u⁻¹ * P.compF v r))) ∧
    HasSum
      (fun η : (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v =>
        (qv v) ^ (-FractionalIdeal.count F v 𝔞) * ‖Hfn (Quotient.out η)‖)
      (∫ x, ‖Hfn x‖ ∂(μ v).μ)
  let F0 : v.adicCompletion F → (G.T v).V := fun x =>
    Fs.f v ((P.loc v).w * (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r)
  let lamU : (G.T v).V →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap ((G.lam v).comp ((G.T v).σa u))
  let c : ℂ := (absFin v u : ℂ) ^ ((1 : ℂ) / 2 + s)
  have hF0 : Integrable F0 (μ v).μ :=
    (intertwine_isSection (P.loc v) (G.T v) (μ v) s hs (Fs.f v) (Fs.f_sec v)).1
      (P.compF v r)
  have hpoint (x : v.adicCompletion F) : Hfn x = c * lamU (F0 x) := by
    have hvec := (Fs.f_sec v).1 0 u
      ((P.loc v).w * (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r)
    have hscalar := congrArg (G.lam v) hvec
    simpa [Hfn, F0, c, lamU, mul_assoc] using hscalar
  have hH : Hfn = fun x => c * lamU (F0 x) := funext hpoint
  have hint : Integrable Hfn (μ v).μ := by
    rw [hH]
    exact (lamU.integrable_comp hF0).const_mul c
  have hperiod (x y : v.adicCompletion F) (hy : y ∈ idealLocalPeriods 𝔞 v) :
      Hfn (x + y) = Hfn x := by
    have hn : (P.loc v).n (Multiplicative.ofAdd (x + y)) =
        (P.loc v).n (Multiplicative.ofAdd x) * (P.loc v).n (Multiplicative.ofAdd y) := by
      rw [ofAdd_add, map_mul]
    have hp := local_scalar_ideal_periods_of_nonzero P G Fs r 𝔞 h𝔞 hfix hΦ v
      ((P.loc v).a u * (P.loc v).w * (P.loc v).n (Multiplicative.ofAdd x)) y hy
    dsimp only [Hfn]
    rw [hn]
    simpa only [mul_assoc] using hp
  obtain ⟨hsum, hnorm⟩ := idealLocalPeriods_integral_cosets 𝔞 v (μ v) Hfn hint hperiod
  have hIntegral : (∫ x, Hfn x ∂(μ v).μ) =
      c * lamU (intertwine (P.loc v) (μ v) (Fs.f v) (P.compF v r)) := by
    rw [hH, integral_const_mul]
    congr 1
    simpa only [F0, intertwine] using ContinuousLinearMap.integral_comp_comm lamU hF0
  let ci : ℂ := (absFin v (u⁻¹ : (v.adicCompletion F)ˣ) : ℂ) ^ ((1 : ℂ) / 2 - s)
  have hM : intertwine (P.loc v) (μ v) (Fs.f v) ((P.loc v).a u⁻¹ * P.compF v r) =
      ci • (G.T v).σa u (intertwine (P.loc v) (μ v) (Fs.f v) (P.compF v r)) := by
    have hm := (intertwine_isSection (P.loc v) (G.T v) (μ v) s hs
      (Fs.f v) (Fs.f_sec v)).2.1 0 u⁻¹ (P.compF v r)
    simpa [ci, TorusRep.weyl, sub_eq_add_neg] using hm
  have heval : G.lam v
        (intertwine (P.loc v) (μ v) (Fs.f v) ((P.loc v).a u⁻¹ * P.compF v r)) =
      ci * lamU (intertwine (P.loc v) (μ v) (Fs.f v) (P.compF v r)) := by
    rw [hM]
    simp [lamU]
  have hqpos : 0 < absFin v u := absFin_pos u.ne_zero
  have hqC : (absFin v u : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hinv : absFin v (u⁻¹ : (v.adicCompletion F)ˣ) = (absFin v u)⁻¹ := by
    simp only [absFin_eq_norm, Units.val_inv_eq_inv_val, norm_inv]
  have hbase : (absFin v (u⁻¹ : (v.adicCompletion F)ˣ) : ℂ) = (absFin v u : ℂ)⁻¹ := by
    rw [hinv, Complex.ofReal_inv]
  have hci : ci = (absFin v u : ℂ) ^ (-((1 : ℂ) / 2 - s)) := by
    dsimp only [ci]
    rw [hbase, Complex.inv_cpow_ofReal_nonneg hqpos.le ((1 : ℂ) / 2 - s),
      ← Complex.cpow_neg]
  have hcoef : (absFin v u : ℂ) * ci = c := by
    calc
      (absFin v u : ℂ) * ci =
          (absFin v u : ℂ) ^ (1 : ℂ) * (absFin v u : ℂ) ^ (-((1 : ℂ) / 2 - s)) := by
        rw [Complex.cpow_one, hci]
      _ = (absFin v u : ℂ) ^ (1 + -((1 : ℂ) / 2 - s)) :=
        (Complex.cpow_add _ _ hqC).symm
      _ = c := by dsimp only [c]; congr 1; ring
  have hfinal : (∫ x, Hfn x ∂(μ v).μ) =
      (absFin v u : ℂ) * G.lam v
        (intertwine (P.loc v) (μ v) (Fs.f v) ((P.loc v).a u⁻¹ * P.compF v r)) := by
    rw [hIntegral, heval, ← hcoef, mul_assoc]
  rw [hfinal] at hsum
  exact ⟨hsum, hnorm⟩

/-- Integration between two restricted-product lifts separates the complex coordinates. -/
theorem scalarOf_arch_integral_product_lifts
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (t r : P.RP) :
    (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
      (P.q t * nInf P x * P.q r)) =
      (∏ᶠ v, G.lam v (Fs.f v (P.compF v (t * r)))) *
        ∏ w, ∫ z : ℂ, Fs.fC w
          (P.compC w t * nC z * P.compC w r) ∧
    (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
      (P.q t * nInf P x * P.q r)‖) =
      ‖∏ᶠ v, G.lam v (Fs.f v (P.compF v (t * r)))‖ *
        ∏ w, ∫ z : ℂ, ‖Fs.fC w
          (P.compC w t * nC z * P.compC w r)‖ := by
  classical
  choose rn hqn hfn hcn using fun x : InfinitePlace F → ℂ =>
    P.nS_components ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  have hfn1 (x : InfinitePlace F → ℂ) (v : FinPlace F) : P.compF v (rn x) = 1 := by
    simpa using hfn x v
  let R (x : InfinitePlace F → ℂ) : P.RP := t * rn x * r
  let cf : ℂ := ∏ᶠ v, G.lam v (Fs.f v (P.compF v (t * r)))
  let fc (w : InfinitePlace F) (z : ℂ) : ℂ :=
    Fs.fC w (P.compC w (t) * nC z * P.compC w r)
  have hq (x : InfinitePlace F → ℂ) :
      P.q (R x) = P.q t * nInf P x * P.q r := by
    simp only [R, map_mul, hqn, nInf]
  have hcompF (x : InfinitePlace F → ℂ) (v : FinPlace F) :
      P.compF v (R x) = P.compF v (t * r) := by
    simp only [R, map_mul, hfn1, mul_one]
  have hcompC (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      P.compC w (R x) = P.compC w (t) * nC (x w) * P.compC w r := by
    simp only [R, map_mul, hcn, nC]
  have hformula (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC (P.q t * nInf P x * P.q r) =
        cf * ∏ w, fc w (x w) := by
    rw [← hq, (scalarOf_q P G Fs (R x)).2]
    simp only [cf, fc, hcompF, hcompC]
  constructor
  · change (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
      (P.q t * nInf P x * P.q r)) = cf * ∏ w, ∫ z : ℂ, fc w z
    calc
      _ = ∫ x : InfinitePlace F → ℂ, cf * ∏ w, fc w (x w) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hformula x
      _ = cf * ∫ x : InfinitePlace F → ℂ, ∏ w, fc w (x w) := integral_const_mul _ _
      _ = _ := by rw [integral_fintype_prod_volume_eq_prod]
  · change (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
      (P.q t * nInf P x * P.q r)‖) = ‖cf‖ * ∏ w, ∫ z : ℂ, ‖fc w z‖
    calc
      _ = ∫ x : InfinitePlace F → ℂ, ‖cf‖ * ∏ w, ‖fc w (x w)‖ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hformula, norm_mul, norm_prod]
      _ = ‖cf‖ * ∫ x : InfinitePlace F → ℂ, ∏ w, ‖fc w (x w)‖ := integral_const_mul _ _
      _ = _ := by
        rw [integral_fintype_prod_volume_eq_prod (fun w (z : ℂ) => ‖fc w z‖)]

/-- The Bruhat integral has explicit local finite factors and a fixed complex factor. -/
theorem scalarOf_bruhat_arch_integral
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (r : P.RP) (δ : Fˣ) (ξ : F) :
    let H : ∀ v : FinPlace F, v.adicCompletion F → ℂ := fun v x =>
      G.lam v (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
        (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r))
    let C : InfinitePlace F → ℂ → ℂ := fun w z => Fs.fC w
      (aC (Units.map w.embedding.toMonoidHom δ) * wC * nC z * P.compC w r)
    (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL δ * weylGL) * nFin P ξ * nInf P x * P.q r)) =
      (∏ᶠ v, H v (algebraMap F (v.adicCompletion F) ξ)) *
        ∏ w, ∫ z : ℂ, C w z ∧
    (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL δ * weylGL) * nFin P ξ * nInf P x * P.q r)‖) =
      ‖∏ᶠ v, H v (algebraMap F (v.adicCompletion F) ξ)‖ *
        ∏ w, ∫ z : ℂ, ‖C w z‖ := by
  classical
  dsimp only
  obtain ⟨u, hqu, hFu, hCu⟩ := nFin_components P ξ
  let t : P.RP := P.ratRP (diagGL δ) * P.ratRP weylGL * u
  have hq : P.q t = P.tc.rat (diagGL δ * weylGL) * nFin P ξ := by
    simp only [t, map_mul, P.q_ratRP, hqu]
  have hweyl {K : Type} [Field K] (φ : F →+* K) :
      Matrix.GeneralLinearGroup.map φ (weylGL (F := F)) = weylM K := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.map, weylGL, weylM]
  have haF (v : FinPlace F) : P.compF v (P.ratRP (diagGL δ)) =
      (P.loc v).a (toLoc v δ) := by
    rw [P.compF_ratRP, scalar_glMap_diagGL, (P.loc v).sec_a]
    rfl
  have hwF (v : FinPlace F) : P.compF v (P.ratRP weylGL) = (P.loc v).w := by
    rw [P.compF_ratRP, hweyl, ← (P.loc v).sec_w]
  have haC (w : InfinitePlace F) : P.compC w (P.ratRP (diagGL δ)) =
      aC (Units.map w.embedding.toMonoidHom δ) := by
    rw [P.compC_ratRP, scalar_glMap_diagGL]
    rfl
  have hwC (w : InfinitePlace F) : P.compC w (P.ratRP weylGL) = wC := by
    rw [P.compC_ratRP, hweyl]
    rfl
  have hcompF (v : FinPlace F) : P.compF v (t * r) =
      (P.loc v).a (toLoc v δ) * (P.loc v).w *
        (P.loc v).n (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F) ξ)) *
          P.compF v r := by
    simp only [t, map_mul, haF, hwF, hFu]
  have hcompC (w : InfinitePlace F) : P.compC w t =
      aC (Units.map w.embedding.toMonoidHom δ) * wC := by
    simp only [t, map_mul, haC, hwC, hCu, mul_one]
  simpa only [hq, hcompF, hcompC] using
    scalarOf_arch_integral_product_lifts P G Fs t r

/-- Local Bruhat period quotients normalize and reindex the rational ideal quotient. -/
theorem bruhat_ideal_quotient_reindex
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (r : P.RP)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC
        (h * ((P.q r)⁻¹ * nFin P ξ * P.q r)) = scalarOf P G Fs.f Fs.fC h)
    (hΦ : ∃ g : P.tc.G, scalarOf P G Fs.f Fs.fC g ≠ 0) (δ : Fˣ) :
    let H : ∀ v : FinPlace F, v.adicCompletion F → ℂ := fun v x =>
      G.lam v (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
        (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r))
    let Q := fun v : FinPlace F => (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v
    let L : ∀ v : FinPlace F, Q v → ℂ := fun v η => H v (Quotient.out η)
    (∃ T : Finset (FinPlace F), ∀ v ∉ T, L v 0 = 1) ∧
    (∑' η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
      ∏ᶠ v, H v (algebraMap F (v.adicCompletion F) (Quotient.out η))) =
      (∑' a : Π₀ v : FinPlace F, Q v, ∏ᶠ v, L v (a v)) ∧
    (Summable (fun η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup =>
      ‖∏ᶠ v, H v (algebraMap F (v.adicCompletion F) (Quotient.out η))‖) ↔
      Summable (fun a : Π₀ v : FinPlace F, Q v => ‖∏ᶠ v, L v (a v)‖)) := by
  classical
  let Hfn : ∀ v : FinPlace F, v.adicCompletion F → ℂ := fun v x =>
    G.lam v (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
      (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r))
  let Q := fun v : FinPlace F => (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v
  let Lfn : ∀ v : FinPlace F, Q v → ℂ := fun v η => Hfn v (Quotient.out η)
  let J := F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup
  let M := Π₀ v : FinPlace F, Q v
  let f (η : J) : ℂ := ∏ᶠ v, Hfn v (algebraMap F (v.adicCompletion F) (Quotient.out η))
  let k (a : M) : ℂ := ∏ᶠ v, Lfn v (a v)
  change (∃ T : Finset (FinPlace F), ∀ v ∉ T, Lfn v 0 = 1) ∧
    (∑' η : J, f η) = (∑' a : M, k a) ∧
    (Summable (fun η : J => ‖f η‖) ↔ Summable (fun a : M => ‖k a‖))
  have hperiod (v : FinPlace F) (x y : v.adicCompletion F)
      (hy : y ∈ idealLocalPeriods 𝔞 v) : Hfn v (x + y) = Hfn v x := by
    dsimp only [Hfn]
    simpa only [ofAdd_add, map_mul, mul_assoc] using
      local_scalar_ideal_periods_of_nonzero P G Fs r 𝔞 h𝔞 hfix hΦ v
        ((P.loc v).a (toLoc v δ) * (P.loc v).w *
          (P.loc v).n (Multiplicative.ofAdd x)) y hy
  have hout0 (v : FinPlace F) :
      Quotient.out (0 : Q v) ∈ idealLocalPeriods 𝔞 v := by
    have hc : (QuotientAddGroup.mk (Quotient.out (0 : Q v)) : Q v) =
        QuotientAddGroup.mk (0 : v.adicCompletion F) :=
      (QuotientAddGroup.out_eq' (0 : Q v)).trans (by simp)
    simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp hc
  have hzero (v : FinPlace F) : Lfn v 0 = Hfn v 0 := by
    simpa only [Lfn, zero_add] using
      hperiod v 0 (Quotient.out (0 : Q v)) (hout0 v)
  let R : P.RP := P.ratRP (diagGL δ) * P.ratRP weylGL * r
  have hweyl {K : Type} [Field K] (φ : F →+* K) :
      Matrix.GeneralLinearGroup.map φ (weylGL (F := F)) = weylM K := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.map, weylGL, weylM]
  have haF (v : FinPlace F) : P.compF v (P.ratRP (diagGL δ)) =
      (P.loc v).a (toLoc v δ) := by
    rw [P.compF_ratRP, scalar_glMap_diagGL, (P.loc v).sec_a]
    rfl
  have hwF (v : FinPlace F) : P.compF v (P.ratRP weylGL) = (P.loc v).w := by
    rw [P.compF_ratRP, hweyl, ← (P.loc v).sec_w]
  have hcompF (v : FinPlace F) : P.compF v R =
      (P.loc v).a (toLoc v δ) * (P.loc v).w * P.compF v r := by
    simp only [R, map_mul, haF, hwF]
  have hraw0 (v : FinPlace F) : Hfn v 0 = G.lam v (Fs.f v (P.compF v R)) := by
    rw [hcompF]
    simp only [Hfn, ofAdd_zero, map_one, mul_one]
  have hfinite : (Function.mulSupport (fun v => Hfn v 0)).Finite := by
    simpa only [hraw0] using (scalarOf_q P G Fs R).1
  obtain ⟨E, hE⟩ := ideal_additive_quotient_equiv 𝔞 h𝔞
  have hclass (η : J) (v : FinPlace F) :
      (QuotientAddGroup.mk (algebraMap F (v.adicCompletion F) (Quotient.out η)) : Q v) =
        E η v := by
    calc
      _ = E (QuotientAddGroup.mk (Quotient.out η)) v := (hE (Quotient.out η) v).symm
      _ = E η v := by rw [QuotientAddGroup.out_eq']
  have hterm (η : J) (v : FinPlace F) :
      Hfn v (algebraMap F (v.adicCompletion F) (Quotient.out η)) = Lfn v (E η v) := by
    let x := algebraMap F (v.adicCompletion F) (Quotient.out η)
    let y := Quotient.out (E η v)
    have hm : x - y ∈ idealLocalPeriods 𝔞 v :=
      QuotientAddGroup.eq_iff_sub_mem.mp
        ((hclass η v).trans (QuotientAddGroup.out_eq' (E η v)).symm)
    change Hfn v x = Hfn v y
    have hxy : x = y + (x - y) := by abel
    rw [hxy]
    exact hperiod v y (x - y) hm
  have hprod (η : J) : f η = k (E η) := by
    dsimp only [f, k]
    exact finprod_congr (hterm η)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hfinite.toFinset, ?_⟩
    intro v hv
    rw [hzero]
    have hvnot : ¬Hfn v 0 ≠ 1 := by
      simpa only [hfinite.mem_toFinset, Function.mem_mulSupport] using hv
    exact not_not.mp hvnot
  · calc
      (∑' η : J, f η) = ∑' η : J, k (E η) := tsum_congr hprod
      _ = ∑' a : M, k a := E.toEquiv.tsum_eq k
  · constructor
    · intro hf
      have hh := hf.comp_injective E.symm.injective
      exact hh.congr fun a => by
        change ‖f (E.symm a)‖ = ‖k a‖
        rw [hprod, E.apply_symm_apply]
    · intro hk
      have hh := hk.comp_injective E.injective
      exact hh.congr fun η => by
        change ‖k (E η)‖ = ‖f η‖
        rw [hprod]

/-- An absolutely summable Bruhat ideal quotient is the product of normalized local intertwines. -/
theorem bruhat_local_quotient_hasProd
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (Fs : GlobalSection P G s) (r : P.RP)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC
        (h * ((P.q r)⁻¹ * nFin P ξ * P.q r)) = scalarOf P G Fs.f Fs.fC h)
    (hΦ : ∃ g : P.tc.G, scalarOf P G Fs.f Fs.fC g ≠ 0) (δ : Fˣ)
    (habs : Summable (fun η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup =>
      ‖∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
        (P.loc v).n (Multiplicative.ofAdd
          (algebraMap F (v.adicCompletion F) (Quotient.out η))) * P.compF v r))‖)) :
    HasProd
      (fun v : FinPlace F =>
        ((((qv v) ^ (-FractionalIdeal.count F v 𝔞) : ℝ) : ℂ)⁻¹) *
          ((absFin v (toLoc v δ) : ℂ) * G.lam v
            (intertwine (P.loc v) (μ v) (Fs.f v)
              ((P.loc v).a (toLoc v δ)⁻¹ * P.compF v r))))
      (∑' η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
        ∏ᶠ v, G.lam v (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
          (P.loc v).n (Multiplicative.ofAdd
            (algebraMap F (v.adicCompletion F) (Quotient.out η))) * P.compF v r))) := by
  classical
  let Hfn : ∀ v : FinPlace F, v.adicCompletion F → ℂ := fun v x =>
    G.lam v (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
      (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r))
  let Q := fun v : FinPlace F => (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v
  let Lfn : ∀ v : FinPlace F, Q v → ℂ := fun v η => Hfn v (Quotient.out η)
  let _ : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let _ : Countable (F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup) :=
    (show Function.Surjective (fun ξ : F =>
      (QuotientAddGroup.mk ξ : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup)) from
      fun η => ⟨Quotient.out η, QuotientAddGroup.out_eq' η⟩).countable
  obtain ⟨E, _⟩ := ideal_additive_quotient_equiv 𝔞 h𝔞
  let _ : Countable (Π₀ v : FinPlace F, Q v) :=
    E.symm.injective.countable
  let _ : ∀ v : FinPlace F, Countable (Q v) := fun v =>
    (DFinsupp.single_injective (β := Q) (i := v)).countable
  obtain ⟨⟨T, hzero⟩, hseries, habstransfer⟩ :=
    bruhat_ideal_quotient_reindex P G Fs r 𝔞 h𝔞 hfix hΦ δ
  have hdirect : Summable (fun a : Π₀ v : FinPlace F, Q v => ‖∏ᶠ v, Lfn v (a v)‖) :=
    habstransfer.mp habs
  have hp := dfinsupp_finprod_hasProd Lfn T hzero hdirect
  have hlocal (v : FinPlace F) :
      (∑' η : Q v, Lfn v η) =
        ((((qv v) ^ (-FractionalIdeal.count F v 𝔞) : ℝ) : ℂ)⁻¹) *
          ((absFin v (toLoc v δ) : ℂ) * G.lam v
            (intertwine (P.loc v) (μ v) (Fs.f v)
              ((P.loc v).a (toLoc v δ)⁻¹ * P.compF v r))) := by
    let mass : ℂ := (((qv v) ^ (-FractionalIdeal.count F v 𝔞) : ℝ) : ℂ)
    let I : ℂ := (absFin v (toLoc v δ) : ℂ) * G.lam v
      (intertwine (P.loc v) (μ v) (Fs.f v)
        ((P.loc v).a (toLoc v δ)⁻¹ * P.compF v r))
    have hmass : mass ≠ 0 := by
      dsimp only [mass]
      exact_mod_cast (zpow_pos (zero_lt_one.trans (qv_gt_one v))
        (-FractionalIdeal.count F v 𝔞)).ne'
    have hc := (local_bruhat_coset_hasSum P G μ hs Fs r 𝔞 h𝔞 hfix hΦ v (toLoc v δ)).1
    change HasSum (fun η : Q v => mass * Lfn v η) I at hc
    have hd := hc.mul_left mass⁻¹
    have hsL : HasSum (Lfn v) (mass⁻¹ * I) := by
      simpa only [← mul_assoc, inv_mul_cancel₀ hmass, one_mul] using hd
    exact hsL.tsum_eq
  simp only [hlocal] at hp
  rw [← hseries] at hp
  exact hp

set_option backward.isDefEq.respectTransparency false in
/-- Extract ideal and spherical corrections from the normalized local Bruhat product. -/
theorem bruhat_intertwine_product_normalization
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (Fs : GlobalSection P G s) (r : P.RP)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (δ : Fˣ) {z : ℂ}
    (hz : HasProd (fun v : FinPlace F =>
      ((((qv v) ^ (-FractionalIdeal.count F v 𝔞) : ℝ) : ℂ)⁻¹) *
        ((absFin v (toLoc v δ) : ℂ) * G.lam v
          (intertwine (P.loc v) (μ v) (Fs.f v)
            ((P.loc v).a (toLoc v δ)⁻¹ * P.compF v r)))) z) :
    let fM : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V := fun v =>
      if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
      else sphWeyl P G v (fun h => hv (Fs.sub h)) s
    z = ((FractionalIdeal.absNorm 𝔞 : ℝ) : ℂ) *
      (∏ᶠ v : FinPlace F, (absFin v (toLoc v δ) : ℂ)) * cprod Fs.T0 s *
        (∏ᶠ v : FinPlace F, G.lam v
          (fM v ((P.loc v).a (toLoc v δ)⁻¹ * P.compF v r))) := by
  classical
  let fM : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V := fun v =>
    if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
    else sphWeyl P G v (fun h => hv (Fs.sub h)) s
  let β : FinPlace F → ℂ := fun v => G.lam v
    (fM v ((P.loc v).a (toLoc v δ)⁻¹ * P.compF v r))
  let m : FinPlace F → ℂ := fun v =>
    (((qv v) ^ (FractionalIdeal.count F v 𝔞) : ℝ) : ℂ)
  let d : FinPlace F → ℂ := fun v => (absFin v (toLoc v δ) : ℂ)
  let b : FinPlace F → ℂ := fun v => if v ∈ Fs.T0 then 1 else cv v s
  let a : FinPlace F → ℂ := fun v => m v * (d v * β v)
  change z = ((FractionalIdeal.absNorm 𝔞 : ℝ) : ℂ) *
    (∏ᶠ v, d v) * cprod Fs.T0 s * (∏ᶠ v, β v)
  let R : P.RP := P.ratRP (diagGL δ⁻¹) * r
  have hcompF (v : FinPlace F) : P.compF v R =
      (P.loc v).a (toLoc v δ)⁻¹ * P.compF v r := by
    dsimp only [R]
    rw [map_mul, P.compF_ratRP, scalar_glMap_diagGL, (P.loc v).sec_a]
    simp only [toLoc, map_inv]
  have hβ : Function.HasFiniteMulSupport β := by
    have hh := (scalarM_q P G μ hs Fs R).1
    simpa only [Function.HasFiniteMulSupport, β, fM, hcompF] using hh
  have hlocal (v : FinPlace F) :
      G.lam v (intertwine (P.loc v) (μ v) (Fs.f v)
        ((P.loc v).a (toLoc v δ)⁻¹ * P.compF v r)) = b v * β v := by
    by_cases hv : v ∈ Fs.T0
    · simp only [b, ite_eq_left hv, β, fM, dite_eq_left hv, one_mul]
    · have hvS : v ∉ S.Sf := fun h => hv (Fs.sub h)
      have hsph := (spherical_section (P.loc v) (P.tame v hvS) (G.T v).weyl
        (G.B v hvS).weyl (fun h => hvS (S.over6 v h)) (-s)).choose_spec
      have hM : intertwine (P.loc v) (μ v) (Fs.f v) =
          cv v s • sphWeyl P G v hvS s :=
        intertwine_spherical (P.loc v) (P.tame v hvS) (G.T v) (G.B v hvS)
          (μ v) (fun h => hvS (S.over6 v h)) s hs
          (Fs.f v) (Fs.f_sec v) (Fs.f_sph v hv).1 (Fs.f_sph v hv).2
          (sphWeyl P G v hvS s) hsph.1 hsph.2.1 hsph.2.2.1
      have heval := congrArg (fun f : (P.loc v).L → (G.T v).V =>
        G.lam v (f ((P.loc v).a (toLoc v δ)⁻¹ * P.compF v r))) hM
      simpa only [b, ite_eq_right hv, β, fM, dite_eq_right hv, Pi.smul_apply,
        map_smul, smul_eq_mul] using heval
  have hm (v : FinPlace F) :
      ((((qv v) ^ (-FractionalIdeal.count F v 𝔞) : ℝ) : ℂ)⁻¹) = m v := by
    simp only [m, zpow_neg, Complex.ofReal_inv, inv_inv]
  have hcounts : (Function.support (fun v : FinPlace F =>
      FractionalIdeal.count F v 𝔞)).Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors 𝔞)
  have hmfinite : Function.HasFiniteMulSupport m := by
    apply hcounts.subset
    intro v hv
    change FractionalIdeal.count F v 𝔞 ≠ 0
    intro hc
    exact hv (by simp only [m, hc, zpow_zero, Complex.ofReal_one])
  have hreal : Function.HasFiniteMulSupport
      (fun v : FinPlace F => absFin v (toLoc v δ)) := by
    have hn : Function.HasFiniteMulSupport
        (fun v : FinPlace F => ‖FinitePlace.embedding v (δ : F)‖) := by
      simpa using finitePlace_mk_hasFiniteMulSupport (Units.ne_zero δ)
    have heq (v : FinPlace F) :
        absFin v (toLoc v δ) = ‖FinitePlace.embedding v (δ : F)‖ := by
      simpa [toLoc] using absFin_algebraMap v (δ : F)
    simpa only [heq] using hn
  have hd : Function.HasFiniteMulSupport d := by
    apply hreal.subset
    intro v hv
    change absFin v (toLoc v δ) ≠ 1
    intro heq
    exact hv (by simp only [d, heq, Complex.ofReal_one])
  have hafinite : Function.HasFiniteMulSupport a := hmfinite.mul (hd.mul hβ)
  have hz' : HasProd (fun v => a v * b v) z := by
    convert hz using 1
    funext v
    rw [hm, hlocal]
    dsimp only [a, d]
    ac_rfl
  have hb : (∏' v, b v) = cprod Fs.T0 s := by
    have hsub := tprod_subtype ({v : FinPlace F | v ∉ Fs.T0})
      (fun v : FinPlace F => cv v s)
    calc
      (∏' v, b v) = ∏' v, ({v : FinPlace F | v ∉ Fs.T0}).mulIndicator
          (fun v => cv v s) v := by
        apply tprod_congr
        intro v
        by_cases hv : v ∈ Fs.T0 <;> simp [b, hv, Set.mulIndicator]
      _ = cprod Fs.T0 s := hsub.symm
  have hmprod : (∏ᶠ v, m v) = ((FractionalIdeal.absNorm 𝔞 : ℝ) : ℂ) := by
    have hfinite : Function.HasFiniteMulSupport (fun v : FinPlace F =>
        ((qv v) ^ (FractionalIdeal.count F v 𝔞) : ℝ)) := by
      apply hcounts.subset
      intro v hv
      change FractionalIdeal.count F v 𝔞 ≠ 0
      intro hc
      exact hv (by simp only [hc, zpow_zero])
    calc
      (∏ᶠ v, m v) = Complex.ofRealHom.toMonoidHom
          (∏ᶠ v : FinPlace F, (qv v) ^ (FractionalIdeal.count F v 𝔞)) :=
        (Complex.ofRealHom.toMonoidHom.map_finprod hfinite).symm
      _ = ((FractionalIdeal.absNorm 𝔞 : ℝ) : ℂ) := by
        rw [← fractionalIdeal_absNorm_finprod 𝔞 h𝔞]
        rfl
  have haprod : (∏ᶠ v, a v) =
      ((FractionalIdeal.absNorm 𝔞 : ℝ) : ℂ) * ((∏ᶠ v, d v) * ∏ᶠ v, β v) := by
    dsimp only [a]
    rw [finprod_mul_distrib (f := m) (g := fun v => d v * β v)
      hmfinite (hd.mul hβ), finprod_mul_distrib (f := d) (g := β) hd hβ, hmprod]
  calc
    z = (∏ᶠ v, a v) * ∏' v, b v := hasProd_finite_factor_tprod a b hafinite hz'
    _ = _ := by rw [haprod, hb]; ac_rfl

/-- Cancel complex Bruhat dilation factors by the global product formula. -/
theorem bruhat_arch_intertwine_product
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (r : P.RP) (δ : Fˣ) :
    (∏ᶠ v : FinPlace F, (absFin v (toLoc v δ) : ℂ)) *
      (∏ w : InfinitePlace F, ∫ z : ℂ, Fs.fC w
        (aC (Units.map w.embedding.toMonoidHom δ) * wC * nC z * P.compC w r)) =
      ∏ w : InfinitePlace F, intertwineC (Fs.fC w)
        (aC (Units.map w.embedding.toMonoidHom δ)⁻¹ * P.compC w r) := by
  classical
  let C : InfinitePlace F → ℂ := fun w =>
    ((‖w.embedding (δ : F)‖ ^ 2 : ℝ) : ℂ)
  let M : InfinitePlace F → ℂ := fun w => intertwineC (Fs.fC w)
    (aC (Units.map w.embedding.toMonoidHom δ)⁻¹ * P.compC w r)
  have hlocal (w : InfinitePlace F) :
      (∫ z : ℂ, Fs.fC w
        (aC (Units.map w.embedding.toMonoidHom δ) * wC * nC z * P.compC w r)) =
        C w * M w := by
    rw [(complex_bruhat_integral (Fs.fC w) (Units.map w.embedding.toMonoidHom δ)
      (P.compC w r)).1]
    simp only [C, M, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, RCLike.real_smul_eq_coe_mul]
    rfl
  have hformula :
      (∏ᶠ v : FinPlace F, (absFin v (toLoc v δ) : ℂ)) *
        (∏ w : InfinitePlace F, C w) = 1 := by
    simpa only [C, Complex.cpow_one, Complex.normSq_eq_norm_sq] using
      scalar_abs_cpow_product D δ (1 : ℂ)
  calc
    _ = (∏ᶠ v : FinPlace F, (absFin v (toLoc v δ) : ℂ)) *
        (∏ w : InfinitePlace F, C w * M w) := by simp_rw [hlocal]
    _ = ((∏ᶠ v : FinPlace F, (absFin v (toLoc v δ) : ℂ)) *
        (∏ w : InfinitePlace F, C w)) * (∏ w : InfinitePlace F, M w) := by
      rw [Finset.prod_mul_distrib]
      ac_rfl
    _ = _ := by rw [hformula, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Normalize the Bruhat product by the ideal-domain covolume to the intertwined scalar. -/
theorem bruhat_scalarM_product_normalization
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (Fs : GlobalSection P G s) (r : P.RP)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (δ : Fˣ) {z : ℂ}
    (hz : HasProd (fun v : FinPlace F =>
      ((((qv v) ^ (-FractionalIdeal.count F v 𝔞) : ℝ) : ℂ)⁻¹) *
        ((absFin v (toLoc v δ) : ℂ) * G.lam v
          (intertwine (P.loc v) (μ v) (Fs.f v)
            ((P.loc v).a (toLoc v δ)⁻¹ * P.compF v r)))) z)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume) :
    ((volume Pd).toReal)⁻¹ •
      (z * ∏ w : InfinitePlace F, ∫ x : ℂ, Fs.fC w
        (aC (Units.map w.embedding.toMonoidHom δ) * wC * nC x * P.compC w r)) =
      scalarM P G μ Fs (P.tc.rat (diagGL δ⁻¹) * P.q r) := by
  classical
  let fM : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V := fun v =>
    if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
    else sphWeyl P G v (fun h => hv (Fs.sub h)) s
  let R : P.RP := P.ratRP (diagGL δ⁻¹) * r
  let N : ℂ := ((FractionalIdeal.absNorm 𝔞 : ℝ) : ℂ)
  let d : ℂ := ∏ᶠ v : FinPlace F, (absFin v (toLoc v δ) : ℂ)
  let β : FinPlace F → ℂ := fun v => G.lam v (fM v (P.compF v R))
  let B : ℂ := ∏ᶠ v : FinPlace F, β v
  let C : ℂ := ∏ w : InfinitePlace F, ∫ x : ℂ, Fs.fC w
    (aC (Units.map w.embedding.toMonoidHom δ) * wC * nC x * P.compC w r)
  let M : ℂ := ∏ w : InfinitePlace F, intertwineC (Fs.fC w) (P.compC w R)
  change ((volume Pd).toReal)⁻¹ • (z * C) =
    scalarM P G μ Fs (P.tc.rat (diagGL δ⁻¹) * P.q r)
  have hq : P.q R = P.tc.rat (diagGL δ⁻¹) * P.q r := by
    simp only [R, map_mul, P.q_ratRP]
  have hcompF (v : FinPlace F) : P.compF v R =
      (P.loc v).a (toLoc v δ)⁻¹ * P.compF v r := by
    dsimp only [R]
    rw [map_mul, P.compF_ratRP, scalar_glMap_diagGL, (P.loc v).sec_a]
    simp only [toLoc, map_inv]
  have hcompC (w : InfinitePlace F) : P.compC w R =
      aC (Units.map w.embedding.toMonoidHom δ)⁻¹ * P.compC w r := by
    dsimp only [R]
    rw [map_mul, P.compC_ratRP, scalar_glMap_diagGL]
    change (QuotientGroup.mk (diagM ℂ (Units.map w.embedding.toMonoidHom δ⁻¹)) :
      PGL2 ℂ) * P.compC w r = _
    simp only [aC, map_inv]
  have hnorm : z = N * d * cprod Fs.T0 s * B := by
    simpa only [N, d, B, β, fM, hcompF] using
      bruhat_intertwine_product_normalization P G μ hs Fs r 𝔞 h𝔞 δ hz
  have harch : d * C = M := by
    simpa only [d, C, M, hcompC] using bruhat_arch_intertwine_product P G Fs r δ
  have hscalar : scalarM P G μ Fs (P.tc.rat (diagGL δ⁻¹) * P.q r) =
      (κF F : ℂ)⁻¹ * cprod Fs.T0 s * (B * M) := by
    have hh := (scalarM_q P G μ hs Fs R).2
    change scalarM P G μ Fs (P.q R) =
      (κF F)⁻¹ * cprod Fs.T0 s * (B * M) at hh
    rw [hq] at hh
    simpa only [Complex.ofReal_inv] using hh
  have hN : N ≠ 0 := by
    have hn : FractionalIdeal.absNorm 𝔞 ≠ 0 :=
      FractionalIdeal.absNorm_eq_zero_iff.not.mpr h𝔞
    dsimp only [N]
    exact_mod_cast hn
  have hvol : ((volume Pd).toReal : ℂ) = (κF F : ℂ) * N := by
    rw [ideal_domain_covolume D 𝔞 h𝔞 Pd hPd, Complex.ofReal_mul]
  calc
    ((volume Pd).toReal)⁻¹ • (z * C) =
        (κF F : ℂ)⁻¹ * (N⁻¹ * N) * cprod Fs.T0 s * (B * (d * C)) := by
      rw [RCLike.real_smul_eq_coe_mul]
      simp only [RCLike.ofReal_inv]
      change ((volume Pd).toReal : ℂ)⁻¹ * (z * C) = _
      rw [hvol, hnorm, mul_inv_rev]
      ac_rfl
    _ = (κF F : ℂ)⁻¹ * cprod Fs.T0 s * (B * M) := by
      rw [inv_mul_cancel₀ hN, mul_one, harch]
    _ = _ := hscalar.symm

set_option backward.isDefEq.respectTransparency false in
/-- Apply local Bruhat product normalization to an absolutely integrable ideal quotient. -/
theorem bruhat_ideal_quotient_integral_eq_scalarM
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (Fs : GlobalSection P G s) (r : P.RP)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC
        (h * ((P.q r)⁻¹ * nFin P ξ * P.q r)) = scalarOf P G Fs.f Fs.fC h)
    (hΦ : ∃ g : P.tc.G, scalarOf P G Fs.f Fs.fC g ≠ 0) (δ : Fˣ)
    (habs : Summable (fun η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup =>
      ∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL δ * weylGL) * nFin P (Quotient.out η) * nInf P x * P.q r)‖))
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume) :
    ((volume Pd).toReal)⁻¹ •
      (∑' η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
        ∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
          (P.tc.rat (diagGL δ * weylGL) * nFin P (Quotient.out η) * nInf P x * P.q r)) =
      scalarM P G μ Fs (P.tc.rat (diagGL δ⁻¹) * P.q r) := by
  classical
  let Q := F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup
  let raw : Q → ℂ := fun η => ∏ᶠ v : FinPlace F, G.lam v
    (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
      (P.loc v).n (Multiplicative.ofAdd
        (algebraMap F (v.adicCompletion F) (Quotient.out η))) * P.compF v r))
  let fc : InfinitePlace F → ℂ → ℂ := fun w x => Fs.fC w
    (aC (Units.map w.embedding.toMonoidHom δ) * wC * nC x * P.compC w r)
  let C : ℂ := ∏ w : InfinitePlace F, ∫ x : ℂ, fc w x
  let Aabs : ℝ := ∏ w : InfinitePlace F, ∫ x : ℂ, ‖fc w x‖
  let I : Q → ℂ := fun η => ∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
    (P.tc.rat (diagGL δ * weylGL) * nFin P (Quotient.out η) * nInf P x * P.q r)
  have hI (η : Q) : I η = raw η * C := by
    simpa only [I, raw, C, fc] using
      (scalarOf_bruhat_arch_integral P G Fs r δ (Quotient.out η)).1
  have hNorm (η : Q) :
      (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL δ * weylGL) * nFin P (Quotient.out η) * nInf P x * P.q r)‖) =
      ‖raw η‖ * Aabs := by
    simpa only [raw, Aabs, fc] using
      (scalarOf_bruhat_arch_integral P G Fs r δ (Quotient.out η)).2
  have hscaled : Summable (fun η : Q => ‖raw η‖ * Aabs) := habs.congr hNorm
  change ((volume Pd).toReal)⁻¹ • (∑' η : Q, I η) =
    scalarM P G μ Fs (P.tc.rat (diagGL δ⁻¹) * P.q r)
  by_cases hA : Aabs = 0
  · have hbound : ‖C‖ ≤ Aabs := by
      dsimp only [C, Aabs]
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun w _ => norm_nonneg _)
        (fun w _ => norm_integral_le_integral_norm _)
    have hC : C = 0 := by
      rw [hA] at hbound
      exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg C))
    have hIz (η : Q) : I η = 0 := by rw [hI, hC, mul_zero]
    let R : P.RP := P.ratRP (diagGL δ⁻¹) * r
    have hq : P.q R = P.tc.rat (diagGL δ⁻¹) * P.q r := by
      simp only [R, map_mul, P.q_ratRP]
    have hcompC (w : InfinitePlace F) : P.compC w R =
        aC (Units.map w.embedding.toMonoidHom δ)⁻¹ * P.compC w r := by
      dsimp only [R]
      rw [map_mul, P.compC_ratRP, scalar_glMap_diagGL]
      change (QuotientGroup.mk (diagM ℂ (Units.map w.embedding.toMonoidHom δ⁻¹)) :
        PGL2 ℂ) * P.compC w r = _
      simp only [aC, map_inv]
    have hM : (∏ w : InfinitePlace F, intertwineC (Fs.fC w) (P.compC w R)) = 0 := by
      have hh := bruhat_arch_intertwine_product P G Fs r δ
      change (∏ᶠ v : FinPlace F, (absFin v (toLoc v δ) : ℂ)) * C =
        (∏ w : InfinitePlace F, intertwineC (Fs.fC w)
          (aC (Units.map w.embedding.toMonoidHom δ)⁻¹ * P.compC w r)) at hh
      rw [hC, mul_zero] at hh
      simpa only [hcompC] using hh.symm
    have hscalar : scalarM P G μ Fs (P.tc.rat (diagGL δ⁻¹) * P.q r) = 0 := by
      have hh := (scalarM_q P G μ hs Fs R).2
      simp only [hM, mul_zero, hq] at hh
      exact hh
    simp only [hIz, tsum_zero, smul_zero, hscalar]
  · have hrawNorm : Summable (fun η : Q => ‖raw η‖) :=
      (summable_mul_right_iff hA).mp hscaled
    have hp := bruhat_local_quotient_hasProd P G μ hs Fs r 𝔞 h𝔞 hfix hΦ δ hrawNorm
    have hsum : (∑' η : Q, I η) = (∑' η : Q, raw η) * C := by
      calc
        _ = ∑' η : Q, raw η * C := tsum_congr hI
        _ = _ := hrawNorm.of_norm.tsum_mul_right C
    rw [hsum]
    simpa only [C, fc] using
      bruhat_scalarM_product_normalization P G μ hs Fs r 𝔞 h𝔞 δ hp Pd hPd

set_option backward.isDefEq.respectTransparency false in
/-- The unfolded big cell equals the intertwined scalar at the inverse quotient class. -/
theorem eisenstein_bigCell_eq_scalarM_on_compact
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (hΦ : ∃ h : P.tc.G, scalarOf P G Fs.f Fs.fC h ≠ 0)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBK : B ⊆ K)
    (hBd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) B volume)
    (δ : Fˣ ⧸ G.Δ) :
    letI : G.Δ.Normal := Subgroup.normal_of_isMulCommutative G.Δ
    letI : CommGroup (Fˣ ⧸ G.Δ) := QuotientGroup.Quotient.commGroup G.Δ
    ((volume B).toReal)⁻¹ •
      (∑' ξ : F, ∫ x in B, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * nInf P x * g)) =
      scalarM P G μ Fs (P.tc.rat (diagGL (Quotient.out (δ⁻¹))) * g) := by
  classical
  letI : G.Δ.Normal := Subgroup.normal_of_isMulCommutative G.Δ
  letI : CommGroup (Fˣ ⧸ G.Δ) := QuotientGroup.Quotient.commGroup G.Δ
  have hs0 : 0 < s.re := (by norm_num : (0 : ℝ) < 1 / 2).trans hs
  obtain ⟨r, hr⟩ := P.q_surj g
  let J := F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup
  let a : Fˣ := (Quotient.out (δ⁻¹))⁻¹
  have ha : (QuotientGroup.mk a : Fˣ ⧸ G.Δ) = δ := by
    simp only [a, QuotientGroup.mk_inv, QuotientGroup.out_eq', inv_inv]
  let ε : Fˣ := (Quotient.out δ) * a⁻¹
  have hε : ε ∈ G.Δ := by
    have heq : (QuotientGroup.mk (Quotient.out δ) : Fˣ ⧸ G.Δ) =
        QuotientGroup.mk a := (QuotientGroup.out_eq' δ).trans ha.symm
    simpa only [ε, div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp heq
  have hdiag (u t : Fˣ) : diagGL (u * t) = diagGL u * diagGL t := by
    apply Units.ext
    ext j l
    fin_cases j <;> fin_cases l <;>
      simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two]
  have hBstar : diagGL ε ∈ Bstar G := by
    change (diagGL ε : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ d ∈ G.Δ, (diagGL ε : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (d : F) * (diagGL ε : Matrix (Fin 2) (Fin 2) F) 1 1
    exact ⟨by simp [diagGL], ε, hε, by simp [diagGL]⟩
  have hmat : diagGL (Quotient.out δ) * weylGL =
      diagGL ε * (diagGL a * weylGL) := by
    have hd : Quotient.out δ = ε * a := by dsimp only [ε]; group
    rw [hd, hdiag, mul_assoc]
  have hrep (h : P.tc.G) :
      scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL (Quotient.out δ) * weylGL) * h) =
      scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL a * weylGL) * h) := by
    rw [hmat, map_mul, mul_assoc]
    exact (scalarOf_invariance P G Fs).1 (diagGL ε) hBstar _
  have hfinite (ξ : F) (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL) * nFin P ξ * nInf P x * g) =
      scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL a * weylGL) * nFin P ξ * nInf P x * g) := by
    simpa only [mul_assoc] using hrep (nFin P ξ * nInf P x * g)
  obtain ⟨hint, habs0, hunfold⟩ :=
    eisenstein_bigCell_unfold_periods P G hs Fs g 𝔞 hfix K hK B hB hBK hBd δ
  have hshift (η : J) := scalarOf_finitePeriod_arch_integral P G Fs g
    (diagGL (Quotient.out δ) * weylGL) (Quotient.out η) (hint η)
  have hnorm (η : J) :
      (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
          nInf P x * g)‖) =
      ∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL a * weylGL) * nFin P (Quotient.out η) * nInf P x * P.q r)‖ := by
    rw [(hshift η).2.2, hr]
    apply integral_congr_ae
    filter_upwards [] with x
    exact congrArg norm (hfinite (Quotient.out η) x)
  have habs : Summable (fun η : J =>
      ∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL a * weylGL) * nFin P (Quotient.out η) * nInf P x * P.q r)‖) :=
    habs0.congr hnorm
  have hcomplex (η : J) :
      (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
          nInf P x * g)) =
      ∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL a * weylGL) * nFin P (Quotient.out η) * nInf P x * P.q r) := by
    rw [(hshift η).2.1, hr]
    apply integral_congr_ae
    filter_upwards [] with x
    exact hfinite (Quotient.out η) x
  have hsum :
      (∑' ξ : F, ∫ x in B, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * nInf P x * g)) =
      ∑' η : J, ∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL a * weylGL) * nFin P (Quotient.out η) * nInf P x * P.q r) :=
    hunfold.trans (tsum_congr hcomplex)
  have hfixR : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * ((P.q r)⁻¹ * nFin P ξ * P.q r)) =
        scalarOf P G Fs.f Fs.fC h := by
    simpa only [hr] using hfix
  have hp := bruhat_ideal_quotient_integral_eq_scalarM P G μ hs0 Fs r
    𝔞 h𝔞 hfixR hΦ a habs B hBd
  rw [hsum]
  simpa only [a, inv_inv, hr] using hp

/-- **eis:constant-term** (KP Prop. II.1.2 replaced): for `Re s > 1/2`, over a period lattice
`𝔞 ⊆ F` (a nonzero fractional ideal) whose finite translations fix all sections at `g`. -/
theorem eisenstein_constantTerm (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume) :
    torusCoeff P (eisenstein P G Fs) g Pd 0 =
      ∑' δ : Fˣ ⧸ G.Δ, (scalarOf P G Fs.f Fs.fC (P.tc.rat (diagGL (Quotient.out δ)) * g) +
        scalarM P G μ Fs (P.tc.rat (diagGL (Quotient.out δ)) * g)) := by
  classical
  letI : G.Δ.Normal := Subgroup.normal_of_isMulCommutative G.Δ
  letI : CommGroup (Fˣ ⧸ G.Δ) := QuotientGroup.Quotient.commGroup G.Δ
  have hs0 : 0 < s.re := (by norm_num : (0 : ℝ) < 1 / 2).trans hs
  by_cases hΦ : ∃ h : P.tc.G, scalarOf P G Fs.f Fs.fC h ≠ 0
  · obtain ⟨B, hB, hK, hBd, _, hvol, hcoef⟩ :=
      eisenstein_zeroCoeff_bounded_domain P G hs Fs g 𝔞 h𝔞 hfix Pd hPd
    obtain ⟨hsmall, hpair, hcoeff⟩ :=
      eisenstein_zeroCoeff_bruhat_on_compact P G hs Fs g
        (closure B) hK B hB subset_closure hvol
    let Q := Fˣ ⧸ G.Δ
    let small : Q → ℂ := fun δ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out δ)) * g)
    let I : Q × F → ℂ := fun p => ∫ x in B, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) * nInf P x * g)
    let M : Q → ℂ := fun δ => scalarM P G μ Fs
      (P.tc.rat (diagGL (Quotient.out δ)) * g)
    let c : ℂ := ((volume B).toReal : ℂ)⁻¹
    let e : Q ≃ Q :=
      { toFun := fun δ => δ⁻¹
        invFun := fun δ => δ⁻¹
        left_inv := fun δ => inv_inv δ
        right_inv := fun δ => inv_inv δ }
    have hsmallS : Summable small := hsmall
    have hpairI : Summable I := hpair
    have houter : Summable (fun δ : Q => ∑' ξ : F, I (δ, ξ)) := hpairI.prod
    have hbig (δ : Q) : c * (∑' ξ : F, I (δ, ξ)) = M (δ⁻¹) := by
      have hh := eisenstein_bigCell_eq_scalarM_on_compact P G μ hs Fs g
        𝔞 h𝔞 hfix hΦ (closure B) hK B hB subset_closure hBd δ
      rw [RCLike.real_smul_eq_coe_mul] at hh
      simp only [RCLike.ofReal_inv] at hh
      change c * (∑' ξ : F, I (δ, ξ)) = M (δ⁻¹) at hh
      exact hh
    have hMI : Summable (fun δ : Q => M (δ⁻¹)) := (houter.mul_left c).congr hbig
    have hM : Summable M := by
      refine (hMI.comp_injective e.injective).congr ?_
      intro δ
      change M ((δ⁻¹)⁻¹) = M δ
      rw [inv_inv]
    have hbigSum : c * (∑' p : Q × F, I p) = ∑' δ : Q, M δ := by
      rw [hpairI.tsum_prod]
      calc
        _ = ∑' δ : Q, c * (∑' ξ : F, I (δ, ξ)) := (houter.tsum_mul_left c).symm
        _ = ∑' δ : Q, M (δ⁻¹) := tsum_congr hbig
        _ = _ := e.tsum_eq M
    calc
      torusCoeff P (eisenstein P G Fs) g Pd 0 =
          torusCoeff P (eisenstein P G Fs) g B 0 := hcoef
      _ = (∑' δ : Q, small δ) + c * (∑' p : Q × F, I p) := hcoeff
      _ = (∑' δ : Q, small δ) + (∑' δ : Q, M δ) := by rw [hbigSum]
      _ = _ := (hsmallS.tsum_add hM).symm
  · push_neg at hΦ
    exact eisenstein_constantTerm_of_zero P G μ hs0 Fs hΦ g Pd

/-- The local Whittaker factor is one outside the exceptional support. -/
theorem whit_good_factor (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s)
    (x : P.RP) (δ : Fˣ) (v : FinPlace F) (hv : v ∉ Fs.T0)
    (hu : IsLocUnit v (toLoc v δ))
    (hk : P.compF v x ∈ (P.tame v (fun h => hv (Fs.sub h))).Kmax) :
    G.lam v ((G.T v).σa (toLoc v δ)
      (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))) = 1 := by
  have hvS : v ∉ S.Sf := fun h => hv (Fs.sub h)
  have hmem : toLoc v δ ∈ G.Alag v :=
    (G.alag_tame v hvS (toLoc v δ)).2 ⟨0, toLoc v δ, hu, by simp⟩
  have hfixed : ∀ z, G.lam v ((G.T v).σa (toLoc v δ) z) = G.lam v z := by
    intro z
    rw [G.lam_equiv v (toLoc v δ) hmem z, G.ω_tame v hvS (toLoc v δ) hmem, one_mul]
  exact whit_good_local_factor (P.loc v) (P.tame v hvS) (G.T v) (G.B v hvS) A (μ v)
    (fun h => hvS (S.over6 v h)) (fun h => hvS (S.different_mem v h)) s (Fs.f v)
    (Fs.f_sec v) (Fs.f_sph v hv).1 (Fs.f_sph v hv).2 (G.lam v) (G.lam_tame v hvS)
    (toLoc v δ) hfixed (P.compF v x) hk

/-- A fixed lift and rational torus element have only finitely many nonidentity factors. -/
theorem whit_finite_mulSupport (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s)
    (x : P.RP) (δ : Fˣ) :
    (Function.mulSupport fun v => G.lam v ((G.T v).σa (toLoc v δ)
      (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v))))).Finite := by
  refine ((Fs.T0.finite_toSet.union (P.comp_restricted x)).union
    (whit_rational_nonunit_finite δ)).subset ?_
  intro v hv
  by_contra hvout
  have hvT : v ∉ Fs.T0 := by
    intro h
    exact hvout (Or.inl (Or.inl h))
  have hvS : v ∉ S.Sf := fun h => hvT (Fs.sub h)
  have hu : IsLocUnit v (toLoc v δ) := by
    by_contra h
    exact hvout (Or.inr h)
  have hk : P.compF v x ∈ (P.tame v hvS).Kmax := by
    by_contra h
    exact hvout (Or.inl (Or.inr ⟨hvS, h⟩))
  exact hv (whit_good_factor P G μ Fs x δ v hvT hu hk)

/-- The unfolded summand evaluated at a specified restricted-product lift. -/
def whitLiftTerm (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s)
    (x : P.RP) (δ : Fˣ ⧸ G.Δ) : ℂ :=
  (∏ᶠ v, G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
    (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v))))) *
    ∏ w, jacquetC (rtr (P.compC w x) (Fs.fC w))

/-- Changing finitely many local Jacquet vectors preserves absolute convergence. -/
theorem whit_jacquet_family_summable (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x : P.RP)
    (E : Finset (FinPlace F)) (hE : Fs.T0 ⊆ E)
    (hcomp : ∀ v (hv : v ∉ E),
      P.compF v x ∈ (P.tame v (fun h => hv (hE (Fs.sub h)))).Kmax)
    (z : ∀ v : FinPlace F, (G.T v).V)
    (hz : ∀ v, v ∉ E → z v =
      jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v))) :
    Summable (fun δ : Fˣ ⧸ G.Δ =>
      ‖∏ᶠ v, G.lam v ((G.T v).σa (toLoc v (Quotient.out δ)) (z v))‖) := by
  have hfin (v : FinPlace F) : Finite ((v.adicCompletion F)ˣ ⧸ G.Alag v) := by
    obtain ⟨w, hw⟩ : ∃ w : (G.T v).V, G.lam v w ≠ 0 := by
      by_contra h
      push Not at h
      apply G.lam_ne v
      ext w
      exact h w
    letI : Nontrivial (G.T v).V := ⟨⟨w, 0, by
      intro h
      apply hw
      rw [h, map_zero]⟩⟩
    exact whit_alag_quotient_finite (G.T v) (G.Alag v) (G.alag_cubes v)
  have hbounds (v : FinPlace F) : ∃ c : ℝ, 0 ≤ c ∧
      ∀ t : (v.adicCompletion F)ˣ, ‖G.lam v ((G.T v).σa t (z v))‖ ≤ c := by
    let R := (G.T v).σa_finite.toFinset
    refine ⟨∑ ρ ∈ R, ‖G.lam v (ρ (z v))‖,
      Finset.sum_nonneg (fun ρ _ => norm_nonneg _), ?_⟩
    intro t
    apply Finset.single_le_sum (f := fun ρ => ‖G.lam v (ρ (z v))‖)
      (a := (G.T v).σa t) (fun ρ _ => norm_nonneg _)
    exact (G.T v).σa_finite.mem_toFinset.mpr ⟨t, rfl⟩
  choose c hc hbound using hbounds
  let a (v : FinPlace F) (δ : Fˣ ⧸ G.Δ) : ℂ :=
    G.lam v ((G.T v).σa (toLoc v (Quotient.out δ)) (z v))
  refine whit_local_product_summable G.Alag E
    (fun v hv => G.alag_tame v (fun h => hv (hE (Fs.sub h))))
    (fun v _ => hfin v) a ?_ (2 * s.re) (by linarith) c
    (fun v _ => hc v) (fun δ v _ => hbound v (toLoc v (Quotient.out δ))) ?_
  · intro δ
    refine (E.finite_toSet.union
      (whit_finite_mulSupport P G μ Fs x (Quotient.out δ))).subset ?_
    intro v hv
    by_cases hvE : v ∈ E
    · exact Or.inl hvE
    · refine Or.inr ?_
      change G.lam v ((G.T v).σa (toLoc v (Quotient.out δ)) (z v)) ≠ 1 at hv
      change G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))) ≠ 1
      simpa only [hz v hvE] using hv
  · intro δ v hv
    have hvT : v ∉ Fs.T0 := fun h => hv (hE h)
    have hvS : v ∉ S.Sf := fun h => hvT (Fs.sub h)
    dsimp [a]
    rw [hz v hv]
    have hdec := (whit_ordv_geometry v).2.2.2.2 (toLoc v (Quotient.out δ))
    have hloc := whit_spherical_factor_norm_le (P.loc v) (P.tame v hvS)
      (G.T v) (G.B v hvS) A (μ v)
      (fun h => hvS (S.over6 v h)) (fun h => hvS (S.different_mem v h))
      s (Fs.f v) (Fs.f_sec v) (Fs.f_sph v hvT).1 (Fs.f_sph v hvT).2
      (G.lam v) (G.lam_tame v hvS)
      (ordv v (toLoc v (Quotient.out δ))) (unitPart v (toLoc v (Quotient.out δ)))
      hdec.1 (P.compF v x) (hcomp v hv)
    rw [← hdec.2] at hloc
    convert hloc using 1 <;> first | rfl | simp only [neg_mul]

/-- Absolute convergence of the unfolded series at any lift. -/
theorem whitLiftTerm_summable (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x : P.RP) :
    Summable (fun δ : Fˣ ⧸ G.Δ => ‖whitLiftTerm P G μ Fs x δ‖) := by
  let E := Fs.T0 ∪ (P.comp_restricted x).toFinset
  have hE : Fs.T0 ⊆ E := Finset.subset_union_left
  have hcomp (v : FinPlace F) (hv : v ∉ E) :
      P.compF v x ∈ (P.tame v (fun h => hv (hE (Fs.sub h)))).Kmax := by
    by_contra hk
    apply hv
    apply Finset.mem_union_right
    exact (P.comp_restricted x).mem_toFinset.mpr
      ⟨(fun h => hv (hE (Fs.sub h))), hk⟩
  have hsum := whit_jacquet_family_summable P G μ hs Fs x E hE hcomp
    (fun v => jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))
    (fun _ _ => rfl)
  simpa only [whitLiftTerm, norm_mul] using
    hsum.mul_right ‖∏ w, jacquetC (rtr (P.compC w x) (Fs.fC w))‖

/-- Central phases of a lift cancel in the local Jacquet product. -/
theorem whit_atLift (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x : P.RP) :
    whittakerE P G μ Fs (P.q x) = (κF F)⁻¹ * ∑' δ, whitLiftTerm P G μ Fs x δ := by
  classical
  let y := Function.surjInv P.q_surj (P.q x)
  have hq : P.q y = P.q x := Function.surjInv_eq P.q_surj (P.q x)
  obtain ⟨ζ, hζ, hprod, hF, hC⟩ := (P.q_eq y x).1 hq
  let ev : rootsOfUnity 3 ℂ →* ℂ :=
    { toFun := fun z => ((z : ℂˣ) : ℂ)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hev : (Function.mulSupport fun v => ev (ζ v)).Finite := by
    refine hζ.subset ?_
    intro v hv
    contrapose! hv
    simp only [Function.mem_mulSupport, not_not] at hv ⊢
    rw [hv, ev.map_one]
  have hevprod : (∏ᶠ v, ev (ζ v)) = 1 := by
    rw [← ev.map_finprod hζ, hprod, ev.map_one]
  have hlocal (δ : Fˣ) (v : FinPlace F) :
      G.lam v ((G.T v).σa (toLoc v δ)
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v y) (Fs.f v)))) =
      ev (ζ v) * G.lam v ((G.T v).σa (toLoc v δ)
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))) := by
    have htr : rtr ((P.loc v).z (ζ v) * P.compF v x) (Fs.f v) =
        rtr ((P.loc v).z (ζ v)) (rtr (P.compF v x) (Fs.f v)) := by
      funext h
      simp only [rtr, mul_assoc]
    rw [hF v, htr, (jacquet_equiv (P.loc v) (G.T v) A (μ v) s
      (rtr (P.compF v x) (Fs.f v)) ((Fs.f_sec v).rtr (P.compF v x))).2 (ζ v)]
    simp only [map_smul, smul_eq_mul]
    rfl
  unfold whittakerE
  apply congrArg (fun z : ℂ => (κF F)⁻¹ * z)
  apply tsum_congr
  intro δ
  change whitLiftTerm P G μ Fs y δ = whitLiftTerm P G μ Fs x δ
  unfold whitLiftTerm
  have hfinite :
      (∏ᶠ v, G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v y) (Fs.f v))))) =
      ∏ᶠ v, G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))) := by
    simp_rw [hlocal]
    rw [finprod_mul_distrib hev (whit_finite_mulSupport P G μ Fs x (Quotient.out δ)),
      hevprod, one_mul]
  rw [hfinite]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  rw [hC w]

open scoped Pointwise in
/-- A nonzero archimedean frequency is a continuous unitary character with zero torus mean. -/
theorem whit_psiInf_character (ν : F) (hν0 : ν ≠ 0) :
    Continuous (psiInf ν) ∧
      (∀ x : InfinitePlace F → ℂ, ‖psiInf ν x‖ = 1) ∧
      (∀ x y : InfinitePlace F → ℂ,
        psiInf ν (x + y) = psiInf ν x * psiInf ν y) ∧
      (∃ t : InfinitePlace F → ℂ, psiInf ν t ≠ 1) ∧
      ∀ (L : AddSubgroup (InfinitePlace F → ℂ)), Countable L →
        ∀ (B : Set (InfinitePlace F → ℂ)), IsAddFundamentalDomain L B volume →
          (∀ t ∈ L, psiInf ν t = 1) → (∫ x in B, psiInf ν x) = 0 := by
  classical
  have hcont : Continuous (psiInf ν) := by
    change Continuous (fun x : InfinitePlace F → ℂ => psiInf ν x)
    simp only [psiInf, psiC]
    fun_prop
  have hnorm (x : InfinitePlace F → ℂ) : ‖psiInf ν x‖ = 1 := by
    simp [psiInf, psiC, Complex.norm_exp]
  have hpsiC (z w : ℂ) : psiC (z + w) = psiC z * psiC w := by
    unfold psiC
    have harg :
        -(4 * Real.pi * Complex.I * ((z + w).re : ℂ)) =
          -(4 * Real.pi * Complex.I * (z.re : ℂ)) +
            -(4 * Real.pi * Complex.I * (w.re : ℂ)) := by
      rw [Complex.add_re, Complex.ofReal_add]
      ring
    rw [harg, Complex.exp_add]
  have hadd (x y : InfinitePlace F → ℂ) :
      psiInf ν (x + y) = psiInf ν x * psiInf ν y := by
    simp only [psiInf, Pi.add_apply, mul_add]
    simp_rw [hpsiC]
    rw [Finset.prod_mul_distrib]
  let w : InfinitePlace F := Classical.arbitrary _
  let t : InfinitePlace F → ℂ :=
    Function.update (fun _ => 0) w ((4 : ℂ)⁻¹ / w.embedding ν)
  have hw : w.embedding ν ≠ 0 := (map_ne_zero w.embedding).mpr hν0
  have hquarter : w.embedding ν * ((4 : ℂ)⁻¹ / w.embedding ν) = (4 : ℂ)⁻¹ := by
    field_simp
  have hphase : psiC ((4 : ℂ)⁻¹) = -1 := by
    unfold psiC
    have hre : (((4 : ℂ)⁻¹).re : ℂ) = (4 : ℂ)⁻¹ := by norm_num
    rw [hre]
    have harg : -(4 * Real.pi * Complex.I * (4 : ℂ)⁻¹) =
        -((Real.pi : ℂ) * Complex.I) := by ring
    rw [harg, Complex.exp_neg_pi_mul_I]
  have htval : psiInf ν t = -1 := by
    unfold psiInf
    rw [Finset.prod_eq_single w]
    · simpa only [t, Function.update_self, hquarter] using hphase
    · intro v _ hvw
      simp [t, hvw, psiC]
    · simp
  have ht : psiInf ν t ≠ 1 := by
    rw [htval]
    norm_num
  refine ⟨hcont, hnorm, hadd, ⟨t, ht⟩, ?_⟩
  intro L hcount B hBd hperiod
  let : Countable L := hcount
  have hsame : (∫ x in B, psiInf ν x) = ∫ x in t +ᵥ B, psiInf ν x := by
    apply hBd.setIntegral_eq (hBd.vadd_of_comm t)
    intro ℓ x
    change psiInf ν ((ℓ : InfinitePlace F → ℂ) + x) = psiInf ν x
    rw [hadd, hperiod ℓ ℓ.property, one_mul]
  have htranslate : (∫ x in t +ᵥ B, psiInf ν x) =
      ∫ x in B, psiInf ν (t + x) := by
    exact (measurePreserving_add_left volume t).setIntegral_image_emb
      (Homeomorph.addLeft t).measurableEmbedding (psiInf ν) B
  have hi : (∫ x in B, psiInf ν x) = psiInf ν t * ∫ x in B, psiInf ν x := by
    calc
      _ = ∫ x in t +ᵥ B, psiInf ν x := hsame
      _ = ∫ x in B, psiInf ν (t + x) := htranslate
      _ = psiInf ν t * ∫ x in B, psiInf ν x := by
        simp_rw [hadd]
        exact integral_const_mul _ _
  have hz : (psiInf ν t - 1) * (∫ x in B, psiInf ν x) = 0 := by
    rw [sub_mul, one_mul, ← hi, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ht)

/-- The weighted Bruhat split on a bounded ideal domain has only big-cell contributions. -/
theorem whit_weighted_bruhat (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1) :
    ∃ B : Set (InfinitePlace F → ℂ), MeasurableSet B ∧ IsCompact (closure B) ∧
      IsAddFundamentalDomain
        ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) B volume ∧
      torusCoeff P (eisenstein P G Fs) g Pd (ν : F) =
        ((volume B).toReal)⁻¹ * ∑' p : (Fˣ ⧸ G.Δ) × F, ∫ u in B,
          scalarOf P G Fs.f Fs.fC
            (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) * nInf P u * g) *
              psiInf (-(ν : F)) u := by
  classical
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F)
    infer_instance
  let : Countable (GL (Fin 2) F) :=
    (Units.val_injective : Function.Injective
      (fun a : GL (Fin 2) F => (a : Matrix (Fin 2) (Fin 2) F))).countable
  let L := (𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom
  have hLcount : Countable L := by
    have hsub : (L : Set (InfinitePlace F → ℂ)) ⊆ Set.range (infEmbA (F := F)) := by
      rintro u ⟨ξ, _, rfl⟩
      exact ⟨ξ, rfl⟩
    exact ((Set.countable_range (infEmbA (F := F))).mono hsub).to_subtype
  obtain ⟨hcont, hnorm, hadd, _, hzero⟩ :=
    whit_psiInf_character (-(ν : F)) (neg_ne_zero.mpr ν.ne_zero)
  have hνneg (ξ : F) (hξ : ξ ∈ (𝔞 : Submodule (𝓞 F) F)) :
      psiInf (-(ν : F)) (infEmbA ξ) = 1 := by
    simpa only [psiInf, infEmbA, RingHom.pi_apply, map_neg, neg_mul, mul_neg] using
      hν (-ξ) ((𝔞 : Submodule (𝓞 F) F).neg_mem hξ)
  have hperiod (u : InfinitePlace F → ℂ) (hu : u ∈ L) :
      psiInf (-(ν : F)) u = 1 := by
    rcases hu with ⟨ξ, hξ, rfl⟩
    exact hνneg ξ hξ
  obtain ⟨B, hB, hBc, hBd, hvol, _, hcompare⟩ :=
    ideal_periodic_domain_comparison D 𝔞 h𝔞 Pd hPd
  have hperiodic : ∀ u ∈ L, ∀ x : InfinitePlace F → ℂ,
      eisenstein P G Fs (nInf P (u + x) * g) * psiInf (-(ν : F)) (u + x) =
        eisenstein P G Fs (nInf P x * g) * psiInf (-(ν : F)) x := by
    intro u hu x
    rw [hadd, hperiod u hu, one_mul]
    rcases hu with ⟨ξ, hξ, rfl⟩
    change eisenstein P G Fs (nInf P (infEmbA ξ + x) * g) * psiInf (-(ν : F)) x =
      eisenstein P G Fs (nInf P x * g) * psiInf (-(ν : F)) x
    rw [eisenstein_ideal_periodic P G hs Fs g 𝔞 hfix ξ hξ x]
  have hdom := hcompare
    (fun x => eisenstein P G Fs (nInf P x * g) * psiInf (-(ν : F)) x) hperiodic
  have hcharZero : (∫ x in B, psiInf (-(ν : F)) x) = 0 :=
    hzero L hLcount B hBd hperiod
  obtain ⟨hint₀, habs₀, _⟩ :=
    eisenstein_integral_tsum_on_compact P G hs Fs g (closure B) hBc B hB subset_closure
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  let f (β : Q) (x : InfinitePlace F → ℂ) : ℂ :=
    scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out β) * nInf P x * g) *
      psiInf (-(ν : F)) x
  have hint (β : Q) : IntegrableOn (f β) B := by
    apply Integrable.mono (hint₀ β)
      ((hint₀ β).aestronglyMeasurable.mul hcont.aestronglyMeasurable)
    filter_upwards [] with x
    simp only [Pi.mul_apply, f, norm_mul, hnorm, mul_one, le_refl]
  have habs : Summable (fun β : Q => ∫ x in B, ‖f β x‖) := by
    simpa only [f, norm_mul, hnorm, mul_one] using habs₀
  have hseries (x : InfinitePlace F → ℂ) :
      eisenstein P G Fs (nInf P x * g) * psiInf (-(ν : F)) x = ∑' β : Q, f β x := by
    simp only [eisenstein, f, Q, mul_assoc, tsum_mul_right]
  let I (β : Q) : ℂ := ∫ x in B, f β x
  have heq : (∫ x in B, eisenstein P G Fs (nInf P x * g) * psiInf (-(ν : F)) x) =
      ∑' β : Q, I β := by
    calc
      _ = ∫ x in B, ∑' β : Q, f β x := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hseries x
      _ = ∑' β : Q, I β := (integral_tsum_of_summable_integral_norm hint habs).symm
  have hsum : Summable I := habs.of_norm_bounded fun β =>
    norm_integral_le_integral_norm _
  obtain ⟨e, hsmall, hbig⟩ := rational_bruhat_coset_equiv P G
  let R : ((Fˣ ⧸ G.Δ) ⊕ ((Fˣ ⧸ G.Δ) × F)) → GL (Fin 2) F :=
    Sum.elim (fun δ => diagGL (Quotient.out δ))
      (fun p => diagGL (Quotient.out p.1) * weylGL * upperGL p.2)
  have he (u) : e u = Quotient.mk (QuotientGroup.rightRel (Bstar G)) (R u) := by
    cases u with
    | inl δ => exact hsmall δ
    | inr p => exact hbig p.1 p.2
  have hrep (u) : I (e u) = ∫ x in B,
      scalarOf P G Fs.f Fs.fC (P.tc.rat (R u) * nInf P x * g) *
        psiInf (-(ν : F)) x := by
    have hb : R u * (Quotient.out (e u))⁻¹ ∈ Bstar G :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact ((Quotient.out_eq (e u)).trans (he u)))
    dsimp only [I, f]
    apply integral_congr_ae
    filter_upwards [] with x
    apply congrArg (fun z : ℂ => z * psiInf (-(ν : F)) x)
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (R u * (Quotient.out (e u))⁻¹) hb
        (P.tc.rat (Quotient.out (e u)) * (nInf P x * g))).symm
  have hsmallI (δ : Fˣ ⧸ G.Δ) : I (e (Sum.inl δ)) = 0 := by
    rw [hrep (Sum.inl δ)]
    simp only [R, Sum.elim_inl]
    simp_rw [scalarOf_diag_unipotent P G Fs]
    rw [integral_const_mul, hcharZero, mul_zero]
  have hbigI (p : (Fˣ ⧸ G.Δ) × F) : I (e (Sum.inr p)) = ∫ x in B,
      scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) * nInf P x * g) *
          psiInf (-(ν : F)) x := by
    simpa only [R, Sum.elim_inr] using hrep (Sum.inr p)
  have hsum' : Summable (fun u => I (e u)) := hsum.comp_injective e.injective
  refine ⟨B, hB, hBc, hBd, ?_⟩
  simp only [torusCoeff, hvol, hdom]
  apply congrArg (fun z : ℂ => ((volume B).toReal)⁻¹ * z)
  calc
    _ = ∑' β : Q, I β := heq
    _ = ∑' u, I (e u) := (e.tsum_eq I).symm
    _ = (∑' δ, I (e (Sum.inl δ))) + ∑' p, I (e (Sum.inr p)) :=
      (hsum'.comp_injective Sum.inl_injective).tsum_sum
        (hsum'.comp_injective Sum.inr_injective)
    _ = _ := by simp only [hsmallI, hbigI, tsum_zero, zero_add]

/-- Ideal-period tiling preserves a Fourier character trivial on the period lattice. -/
theorem whit_bigCell_unfold_periods
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hfix : ∀ α ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P α * g)) = scalarOf P G Fs.f Fs.fC h)
    (K : Set (InfinitePlace F → ℂ)) (hK : IsCompact K)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBK : B ⊆ K)
    (hBd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) B volume)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
      psiInf (ν : F) (infEmbA ξ) = 1)
    (δ : Fˣ ⧸ G.Δ) :
    (∀ η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
      Integrable (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
          nInf P x * g) * psiInf (-(ν : F)) x)) ∧
    Summable (fun η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup =>
      ∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
          nInf P x * g)‖) ∧
    (∑' ξ : F, ∫ x in B, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * nInf P x * g) *
        psiInf (-(ν : F)) x) =
      ∑' η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
        ∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
          (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL (Quotient.out η)) *
            nInf P x * g) * psiInf (-(ν : F)) x := by
  classical
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let J := (𝔞 : Submodule (𝓞 F) F).toAddSubgroup
  let Q := F ⧸ J
  let base (ξ : F) (x : InfinitePlace F → ℂ) : ℂ := scalarOf P G Fs.f Fs.fC
    (P.tc.rat (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * nInf P x * g)
  let f (ξ : F) (x : InfinitePlace F → ℂ) : ℂ :=
    base ξ x * psiInf (-(ν : F)) x
  obtain ⟨hχcont, hχnorm, hχadd, _, _⟩ :=
    whit_psiInf_character (-(ν : F)) (neg_ne_zero.mpr ν.ne_zero)
  have hnorm (ξ : F) (x : InfinitePlace F → ℂ) : ‖f ξ x‖ = ‖base ξ x‖ := by
    simp only [f, norm_mul, hχnorm, mul_one]
  have hνneg (ξ : F) (hξ : ξ ∈ (𝔞 : Submodule (𝓞 F) F)) :
      psiInf (-(ν : F)) (infEmbA ξ) = 1 := by
    simpa only [psiInf, infEmbA, RingHom.pi_apply, map_neg, neg_mul, mul_neg] using
      hν (-ξ) ((𝔞 : Submodule (𝓞 F) F).neg_mem hξ)
  obtain ⟨e, _, hbig⟩ := rational_bruhat_coset_equiv P G
  obtain ⟨_, habs, _⟩ := eisenstein_integral_tsum_on_compact P G hs Fs g K hK B hB hBK
  have hrep (ξ : F) (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out (e (Sum.inr (δ, ξ)))) * nInf P x * g) = base ξ x := by
    let γ := diagGL (Quotient.out δ) * weylGL * upperGL ξ
    have hb : γ * (Quotient.out (e (Sum.inr (δ, ξ))))⁻¹ ∈ Bstar G :=
      QuotientGroup.rightRel_apply.mp
        (Quotient.exact ((Quotient.out_eq (e (Sum.inr (δ, ξ)))).trans (hbig δ ξ)))
    dsimp only [base]
    simpa only [γ, map_mul, map_inv, mul_assoc, inv_mul_cancel_left] using
      ((scalarOf_invariance P G Fs).1 (γ * (Quotient.out (e (Sum.inr (δ, ξ))))⁻¹) hb
        (P.tc.rat (Quotient.out (e (Sum.inr (δ, ξ)))) * (nInf P x * g))).symm
  have hrepNorm (ξ : F) :
      (∫ x in B, ‖scalarOf P G Fs.f Fs.fC
        (P.tc.rat (Quotient.out (e (Sum.inr (δ, ξ)))) * nInf P x * g)‖) =
        ∫ x in B, ‖f ξ x‖ := by
    simp_rw [hnorm]
    apply integral_congr_ae
    filter_upwards [] with x
    exact congrArg norm (hrep ξ x)
  have hinj : Function.Injective (fun ξ : F => e (Sum.inr (δ, ξ))) :=
    e.injective.comp (Sum.inr_injective.comp (Prod.mk_right_injective δ))
  have hnormSeries : Summable (fun ξ : F => ∫ x in B, ‖f ξ x‖) :=
    (habs.comp_injective hinj).congr hrepNorm
  have hcomplexSeries : Summable (fun ξ : F => ∫ x in B, f ξ x) :=
    hnormSeries.of_norm_bounded fun ξ => norm_integral_le_integral_norm _
  have hcont (ξ : F) : Continuous (f ξ) :=
    (scalarOf_unipotent_continuous P G Fs g
      (diagGL (Quotient.out δ) * weylGL * upperGL ξ)).mul hχcont
  have hupper (u v : F) : upperGL (u + v) = upperGL u * upperGL v := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperGL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hbasePeriod (ξ : F) (α : J) (x : InfinitePlace F → ℂ) :
      base (ξ + (α : F)) x = base ξ (infEmbA (α : F) + x) := by
    dsimp only [base]
    have hm : diagGL (Quotient.out δ) * weylGL * upperGL (ξ + (α : F)) =
        (diagGL (Quotient.out δ) * weylGL * upperGL ξ) * upperGL (α : F) := by
      simp only [hupper, mul_assoc]
    rw [hm]
    exact scalarOf_rational_period_translate P G Fs g
      (diagGL (Quotient.out δ) * weylGL * upperGL ξ) (α : F) x
      (hfix (α : F) α.property)
  have hperiod (ξ : F) (α : J) (x : InfinitePlace F → ℂ) :
      f (ξ + (α : F)) x = f ξ (infEmbA (α : F) + x) := by
    dsimp only [f]
    rw [hbasePeriod, hχadd, hνneg (α : F) α.property, one_mul]
  let r (p : Q × J) : F := Quotient.out p.1 + (p.2 : F)
  have hrclass (p : Q × J) : (QuotientAddGroup.mk (r p) : Q) = p.1 := by
    calc
      _ = QuotientAddGroup.mk (Quotient.out p.1) := by
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        have hd : r p - Quotient.out p.1 = (p.2 : F) := by dsimp only [r]; abel
        simpa only [hd] using p.2.property
      _ = p.1 := QuotientAddGroup.out_eq' p.1
  have hrbij : Function.Bijective r := by
    constructor
    · intro p q hpq
      have hq : p.1 = q.1 := by
        calc
          p.1 = (QuotientAddGroup.mk (r p) : Q) := (hrclass p).symm
          _ = QuotientAddGroup.mk (r q) := congrArg (fun z : F => (QuotientAddGroup.mk z : Q)) hpq
          _ = q.1 := hrclass q
      have ha : p.2 = q.2 := by
        apply Subtype.ext
        dsimp only [r] at hpq
        rw [hq] at hpq
        exact add_left_cancel hpq
      exact Prod.ext hq ha
    · intro ξ
      let η : Q := QuotientAddGroup.mk ξ
      have ha : ξ - Quotient.out η ∈ J :=
        QuotientAddGroup.eq_iff_sub_mem.mp ((QuotientAddGroup.out_eq' η).symm)
      refine ⟨(η, ⟨ξ - Quotient.out η, ha⟩), ?_⟩
      change Quotient.out η + (ξ - Quotient.out η) = ξ
      abel
  let ep : F ≃ Q × J := (Equiv.ofBijective r hrbij).symm
  have hep (p : Q × J) : ep.symm p = Quotient.out p.1 + (p.2 : F) := rfl
  have hpairNorm : Summable (fun p : Q × J =>
      ∫ x in B, ‖f (Quotient.out p.1 + (p.2 : F)) x‖) := by
    simpa only [Function.comp_def, hep] using hnormSeries.comp_injective ep.symm.injective
  have hshiftNorm (p : Q × J) :
      (∫ x in B, ‖f (Quotient.out p.1 + (p.2 : F)) x‖) =
        ∫ x in B, ‖f (Quotient.out p.1) (infEmbA (p.2 : F) + x)‖ := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact congrArg norm (hperiod (Quotient.out p.1) p.2 x)
  have htranslatedNorm : Summable (fun p : Q × J =>
      ∫ x in B, ‖f (Quotient.out p.1) (infEmbA (p.2 : F) + x)‖) :=
    hpairNorm.congr hshiftNorm
  have ht (η : Q) : Integrable (f (Quotient.out η)) ∧
      (∫ x : InfinitePlace F → ℂ, f (Quotient.out η) x) =
        ∑' α : J, ∫ x in B, f (Quotient.out η) (infEmbA (α : F) + x) :=
    ideal_domain_integral_tiling 𝔞 K hK B hB hBK hBd
      (f (Quotient.out η)) (hcont (Quotient.out η)) (htranslatedNorm.prod_factor η)
  have hpairComplex : Summable (fun p : Q × J => ∫ x in B, f (ep.symm p) x) :=
    hcomplexSeries.comp_injective ep.symm.injective
  refine ⟨?_, ?_, ?_⟩
  · intro η
    exact (ht η).1
  · exact (eisenstein_bigCell_unfold_periods P G hs Fs g 𝔞 hfix
      K hK B hB hBK hBd δ).2.1
  · change (∑' ξ : F, ∫ x in B, f ξ x) =
      ∑' η : Q, ∫ x : InfinitePlace F → ℂ, f (Quotient.out η) x
    calc
      _ = ∑' p : Q × J, ∫ x in B, f (ep.symm p) x := (ep.symm.tsum_eq _).symm
      _ = ∑' η : Q, ∑' α : J, ∫ x in B, f (ep.symm (η, α)) x := hpairComplex.tsum_prod
      _ = _ := by
        apply tsum_congr
        intro η
        calc
          _ = ∑' α : J, ∫ x in B, f (Quotient.out η) (infEmbA (α : F) + x) := by
            apply tsum_congr
            intro α
            rw [hep]
            apply integral_congr_ae
            filter_upwards [] with x
            exact hperiod (Quotient.out η) α x
          _ = _ := (ht η).2.symm

/-- Shifting a rational unipotent to finite coordinates records its Fourier character. -/
theorem whit_finitePeriod_arch_integral
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G)
    (γ : GL (Fin 2) F) (ξ : F) (ν : Fˣ)
    (hint : Integrable (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL ξ) * nInf P x * g) * psiInf (-(ν : F)) x)) :
    Integrable (fun x : InfinitePlace F → ℂ => scalarOf P G Fs.f Fs.fC
      (P.tc.rat γ * nFin P ξ * nInf P x * g) * psiInf (-(ν : F)) x) ∧
    (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL ξ) * nInf P x * g) * psiInf (-(ν : F)) x) =
      psiInf (ν : F) (infEmbA ξ) *
        (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
          (P.tc.rat γ * nFin P ξ * nInf P x * g) * psiInf (-(ν : F)) x) := by
  classical
  have hni (y z : InfinitePlace F → ℂ) : nInf P (y + z) = nInf P y * nInf P z := by
    dsimp only [nInf]
    have hp : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y + z) =
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y) +
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), z) := by simp
    rw [hp, ofAdd_add, map_mul]
  have hfactor (x : InfinitePlace F → ℂ) :
      P.tc.rat γ * nFin P ξ * nInf P x * g =
        P.tc.rat (γ * upperGL ξ) * nInf P (-infEmbA ξ + x) * g := by
    dsimp only [nFin]
    calc
      _ = (P.tc.rat γ * P.tc.rat (upperGL ξ)) *
          (nInf P (-infEmbA ξ) * nInf P x) * g := by group
      _ = (P.tc.rat γ * P.tc.rat (upperGL ξ)) *
          nInf P (-infEmbA ξ + x) * g := by rw [← hni]
      _ = _ := by rw [map_mul]
  obtain ⟨_, hχnorm, hχadd, _, _⟩ :=
    whit_psiInf_character (-(ν : F)) (neg_ne_zero.mpr ν.ne_zero)
  have hsign : psiInf (-(ν : F)) (-infEmbA ξ) = psiInf (ν : F) (infEmbA ξ) := by
    simp only [psiInf, map_neg, Pi.neg_apply, neg_mul, mul_neg, neg_neg]
  let c : ℂ := psiInf (ν : F) (infEmbA ξ)
  have hcnorm : ‖c‖ = 1 := by
    dsimp only [c]
    rw [← hsign]
    exact hχnorm (-infEmbA ξ)
  have hc : c ≠ 0 := by
    intro h
    simpa only [h, norm_zero, zero_ne_one] using hcnorm
  let rationalKernel (x : InfinitePlace F → ℂ) : ℂ :=
    scalarOf P G Fs.f Fs.fC
      (P.tc.rat (γ * upperGL ξ) * nInf P x * g) * psiInf (-(ν : F)) x
  let finiteKernel (x : InfinitePlace F → ℂ) : ℂ :=
    scalarOf P G Fs.f Fs.fC
      (P.tc.rat γ * nFin P ξ * nInf P x * g) * psiInf (-(ν : F)) x
  have hshift (x : InfinitePlace F → ℂ) :
      rationalKernel (-infEmbA ξ + x) = c * finiteKernel x := by
    dsimp only [rationalKernel, finiteKernel, c]
    rw [hfactor, hχadd, hsign]
    ring
  have hrightfun : finiteKernel =
      fun x : InfinitePlace F → ℂ => c⁻¹ * rationalKernel (-infEmbA ξ + x) := by
    funext x
    rw [hshift, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hleft : Integrable rationalKernel := hint
  have hright : Integrable finiteKernel := by
    rw [hrightfun]
    exact (hleft.comp_add_left (-infEmbA ξ)).const_mul c⁻¹
  change Integrable finiteKernel ∧
    (∫ x : InfinitePlace F → ℂ, rationalKernel x) =
      c * ∫ x : InfinitePlace F → ℂ, finiteKernel x
  refine ⟨hright, ?_⟩
  calc
    _ = ∫ x : InfinitePlace F → ℂ, rationalKernel (-infEmbA ξ + x) :=
      (integral_add_left_eq_self rationalKernel (-infEmbA ξ)).symm
    _ = ∫ x : InfinitePlace F → ℂ, c * finiteKernel x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hshift
    _ = _ := integral_const_mul c finiteKernel

/-- On rational arguments the archimedean character equals the finite negative-character product. -/
theorem whit_rational_character_product (D : FieldData F) (A : AddCharData F)
    (ν ξ : F) :
    Function.HasFiniteMulSupport (fun v : FinPlace F =>
      A.ψ v (-algebraMap F (v.adicCompletion F) (ν * ξ))) ∧
    psiInf ν (infEmbA ξ) =
      ∏ᶠ v : FinPlace F, A.ψ v (-algebraMap F (v.adicCompletion F) (ν * ξ)) := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  have harch : psiInf ν (infEmbA ξ) =
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F (ν * ξ) : ℂ))) := by
    simpa only [psiInf, infEmbA, RingHom.pi_apply, map_mul, psiC] using
      ArtinPrimitiveRoots.Proofs.a1_dual_p.arch_product_eq_trace (ν * ξ)
  have htrace : (Algebra.trace ℚ F (-(ν * ξ)) : ℂ) =
      -(Algebra.trace ℚ F (ν * ξ) : ℂ) := by
    simp only [map_neg, Rat.cast_neg]
  have hneg : Complex.exp
      (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F (-(ν * ξ)) : ℂ))) =
        (psiInf ν (infEmbA ξ))⁻¹ := by
    rw [htrace, harch, ← Complex.exp_neg]
    congr 1
    ring
  have hc : psiInf ν (infEmbA ξ) ≠ 0 := by
    rw [harch]
    exact Complex.exp_ne_zero _
  obtain ⟨hfinite, hglobal⟩ := A.trivial_on_F (-(ν * ξ))
  have hrelation : (∏ᶠ v : FinPlace F,
      A.ψ v (-algebraMap F (v.adicCompletion F) (ν * ξ))) *
        (psiInf ν (infEmbA ξ))⁻¹ = 1 := by
    rw [hneg] at hglobal
    simpa only [map_neg] using hglobal
  refine ⟨?_, ?_⟩
  · simpa only [Function.HasFiniteMulSupport, map_neg] using hfinite
  · have h := congrArg (fun z : ℂ => z * psiInf ν (infEmbA ξ)) hrelation
    simpa only [mul_assoc, inv_mul_cancel₀ hc, mul_one, one_mul] using h.symm

/-- Dual rational ideal periods force the frequency character to be trivial locally. -/
theorem whit_local_ideal_character (D : FieldData F) (A : AddCharData F)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
      psiInf (ν : F) (infEmbA ξ) = 1)
    (v : FinPlace F) (y : v.adicCompletion F) (hy : y ∈ idealLocalPeriods 𝔞 v) :
    A.ψ v (-((toLoc v ν : v.adicCompletion F) * y)) = 1 := by
  classical
  let I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
    (toPrincipalIdeal (𝓞 F) F ν : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  let c : FinPlace F → ℤ := fun u => FractionalIdeal.count F u I
  let e : FinPlace F → ℤ := fun u => -c u
  have hc : (Function.support c).Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  have he : (Function.support e).Finite := by
    apply hc.subset
    intro u hu
    change -c u ≠ 0 at hu
    exact neg_ne_zero.mp hu
  have hnorm (u : FinPlace F) :
      absFin u (toLoc u ν : u.adicCompletion F) = (qv u) ^ (-c u) := by
    have hval : Valued.v (toLoc u ν : u.adicCompletion F) = WithZero.exp (-c u) := by
      change Valued.v ((ν : F) : u.adicCompletion F) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      dsimp only [c, I]
      rw [FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation, neg_neg]
      exact (WithZero.exp_log ((u.valuation F).ne_zero_iff.mpr ν.ne_zero)).symm
    rw [absFin_eq_norm, FinitePlace.norm_def, hval,
      WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero u) (by simp),
      WithZero.toAdd_unzero_eq_log (by simp)]
    simp [qv]
  let x : ∀ u : FinPlace F, u.adicCompletion F := Pi.single v y
  have hx : ∀ u : FinPlace F, x u ∈ idealLocalPeriods 𝔞 u := by
    intro u
    by_cases hu : u = v
    · subst u
      simpa only [x, Pi.single_eq_same] using hy
    · have hx0 : x u = 0 := by simp [x, hu]
      rw [hx0]
      exact (idealLocalPeriods 𝔞 u).zero_mem
  obtain ⟨ξ, hξmem, happ⟩ := ideal_period_additive_approximation 𝔞 h𝔞 x hx e he
  let ε (u : FinPlace F) : u.adicCompletion F := x u - algebraMap F (u.adicCompletion F) ξ
  have herr (u : FinPlace F) :
      absFin u (ε u) ≤ (qv u) ^ c u := by
    simpa only [ε, e, neg_neg] using happ u
  have hint (u : FinPlace F) :
      -((toLoc u ν : u.adicCompletion F) * ε u) ∈ u.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff]
    calc
      ‖-((toLoc u ν : u.adicCompletion F) * ε u)‖ =
          (qv u) ^ (-c u) * absFin u (ε u) := by
        rw [norm_neg, norm_mul, ← absFin_eq_norm u (toLoc u ν : u.adicCompletion F),
          hnorm, ← absFin_eq_norm u (ε u)]
      _ ≤ (qv u) ^ (-c u) * (qv u) ^ c u :=
        mul_le_mul_of_nonneg_left (herr u)
          (zpow_nonneg (zero_lt_one.trans (qv_gt_one u)).le _)
      _ = 1 := by
        rw [← zpow_add₀ (zero_lt_one.trans (qv_gt_one u)).ne', neg_add_cancel, zpow_zero]
  have hψerr (u : FinPlace F) :
      A.ψ u (-((toLoc u ν : u.adicCompletion F) * ε u)) = 1 :=
    A.integral u _ (hint u)
  have hco (u : FinPlace F) :
      (toLoc u ν : u.adicCompletion F) = algebraMap F (u.adicCompletion F) (ν : F) := rfl
  have hpoint (u : FinPlace F) :
      A.ψ u (-((toLoc u ν : u.adicCompletion F) * x u)) =
        A.ψ u (-algebraMap F (u.adicCompletion F) ((ν : F) * ξ)) := by
    have harg : -((toLoc u ν : u.adicCompletion F) * x u) =
        -algebraMap F (u.adicCompletion F) ((ν : F) * ξ) +
          -((toLoc u ν : u.adicCompletion F) * ε u) := by
      rw [map_mul, ← hco u]
      dsimp only [ε]
      ring
    rw [harg, (A.ψ u).map_add_eq_mul, hψerr, mul_one]
  have hprod : (∏ᶠ u : FinPlace F,
      A.ψ u (-((toLoc u ν : u.adicCompletion F) * x u))) = 1 := by
    calc
      _ = ∏ᶠ u : FinPlace F,
          A.ψ u (-algebraMap F (u.adicCompletion F) ((ν : F) * ξ)) := finprod_congr hpoint
      _ = psiInf (ν : F) (infEmbA ξ) := (whit_rational_character_product D A (ν : F) ξ).2.symm
      _ = 1 := hν ξ hξmem
  have hsingle := finprod_eq_single
    (fun u : FinPlace F => A.ψ u (-((toLoc u ν : u.adicCompletion F) * x u))) v
    (by intro u hu; simp [x, hu])
  simpa only [x, Pi.single_eq_same] using hsingle.symm.trans hprod

/-- Fourier-weighted integration separates the complex coordinates of two lifts. -/
theorem whit_arch_integral_product_lifts
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (t r : P.RP) (ν : F) :
    (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
      (P.q t * nInf P x * P.q r) * psiInf (-ν) x) =
      (∏ᶠ v, G.lam v (Fs.f v (P.compF v (t * r)))) *
        ∏ w, ∫ z : ℂ, psiC (-(w.embedding ν * z)) * Fs.fC w
          (P.compC w t * nC z * P.compC w r) ∧
    (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
      (P.q t * nInf P x * P.q r) * psiInf (-ν) x‖) =
      ‖∏ᶠ v, G.lam v (Fs.f v (P.compF v (t * r)))‖ *
        ∏ w, ∫ z : ℂ, ‖psiC (-(w.embedding ν * z)) * Fs.fC w
          (P.compC w t * nC z * P.compC w r)‖ := by
  classical
  choose rn hqn hfn hcn using fun x : InfinitePlace F → ℂ =>
    P.nS_components ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
  have hfn1 (x : InfinitePlace F → ℂ) (v : FinPlace F) : P.compF v (rn x) = 1 := by
    simpa using hfn x v
  let R (x : InfinitePlace F → ℂ) : P.RP := t * rn x * r
  let cf : ℂ := ∏ᶠ v, G.lam v (Fs.f v (P.compF v (t * r)))
  let fc (w : InfinitePlace F) (z : ℂ) : ℂ :=
    psiC (-(w.embedding ν * z)) * Fs.fC w
      (P.compC w t * nC z * P.compC w r)
  have hq (x : InfinitePlace F → ℂ) :
      P.q (R x) = P.q t * nInf P x * P.q r := by
    simp only [R, map_mul, hqn, nInf]
  have hcompF (x : InfinitePlace F → ℂ) (v : FinPlace F) :
      P.compF v (R x) = P.compF v (t * r) := by
    simp only [R, map_mul, hfn1, mul_one]
  have hcompC (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      P.compC w (R x) = P.compC w t * nC (x w) * P.compC w r := by
    simp only [R, map_mul, hcn, nC]
  have hscalar (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC (P.q t * nInf P x * P.q r) =
        cf * ∏ w, Fs.fC w (P.compC w t * nC (x w) * P.compC w r) := by
    rw [← hq, (scalarOf_q P G Fs (R x)).2]
    simp only [cf, hcompF, hcompC]
  have hpsi (x : InfinitePlace F → ℂ) :
      psiInf (-ν) x = ∏ w, psiC (-(w.embedding ν * x w)) := by
    simp only [psiInf, map_neg, neg_mul]
  have hformula (x : InfinitePlace F → ℂ) :
      scalarOf P G Fs.f Fs.fC (P.q t * nInf P x * P.q r) * psiInf (-ν) x =
        cf * ∏ w, fc w (x w) := by
    rw [hscalar, hpsi, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro w hw
    exact mul_comm _ _
  constructor
  · change (∫ x : InfinitePlace F → ℂ, scalarOf P G Fs.f Fs.fC
      (P.q t * nInf P x * P.q r) * psiInf (-ν) x) = cf * ∏ w, ∫ z : ℂ, fc w z
    calc
      _ = ∫ x : InfinitePlace F → ℂ, cf * ∏ w, fc w (x w) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hformula x
      _ = cf * ∫ x : InfinitePlace F → ℂ, ∏ w, fc w (x w) := integral_const_mul _ _
      _ = _ := by rw [integral_fintype_prod_volume_eq_prod]
  · change (∫ x : InfinitePlace F → ℂ, ‖scalarOf P G Fs.f Fs.fC
      (P.q t * nInf P x * P.q r) * psiInf (-ν) x‖) = ‖cf‖ * ∏ w, ∫ z : ℂ, ‖fc w z‖
    calc
      _ = ∫ x : InfinitePlace F → ℂ, ‖cf‖ * ∏ w, ‖fc w (x w)‖ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hformula, norm_mul, norm_prod]
      _ = ‖cf‖ * ∫ x : InfinitePlace F → ℂ, ∏ w, ‖fc w (x w)‖ := integral_const_mul _ _
      _ = _ := by
        rw [integral_fintype_prod_volume_eq_prod (fun w (z : ℂ) => ‖fc w z‖)]

/-- An identically zero scalar section has zero Whittaker summands at every lift. -/
theorem whitLiftTerm_eq_zero_of_scalarOf_eq_zero
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s)
    (hzero : ∀ g : P.tc.G, scalarOf P G Fs.f Fs.fC g = 0)
    (x : P.RP) (δ : Fˣ ⧸ G.Δ) : whitLiftTerm P G μ Fs x δ = 0 := by
  classical
  have hs0 : 0 < s.re := by linarith
  unfold whitLiftTerm
  rcases scalarOf_zero_has_zero_factor P G Fs hzero with ⟨v, hv, hlocal⟩ | ⟨w, harch⟩
  · let b : (v.adicCompletion F)ˣ := toLoc v (Quotient.out δ)
    let c : ℂ := (absFin v b : ℂ) ^ ((1 : ℂ) / 2 + s)
    have hb : (absFin v b : ℂ) ≠ 0 := by
      exact_mod_cast (absFin_pos b.ne_zero).ne'
    have hc : c ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hb)
    have htwisted (k : (P.loc v).L) :
        G.lam v ((G.T v).σa b (Fs.f v k)) = 0 := by
      have h := congrArg (G.lam v) ((Fs.f_sec v).1 0 b k)
      have hrel : c * G.lam v ((G.T v).σa b (Fs.f v k)) = 0 := by
        simpa [c, hlocal] using h.symm
      exact (mul_eq_zero.mp hrel).resolve_left hc
    let lam : (G.T v).V →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((G.lam v).comp ((G.T v).σa b))
    let f : (P.loc v).L → (G.T v).V := rtr (P.compF v x) (Fs.f v)
    have hJ := whit_local_jacquet_integral (P.loc v) (G.T v) A (μ v) hs0 f
      ((Fs.f_sec v).rtr (P.compF v x))
    have hfun : (fun u : v.adicCompletion F =>
        lam (A.ψ v (-u) • f ((P.loc v).w * (P.loc v).n (Multiplicative.ofAdd u)))) =
          fun _ => (0 : ℂ) := by
      funext u
      change G.lam v ((G.T v).σa b (A.ψ v (-u) • Fs.f v
        (((P.loc v).w * (P.loc v).n (Multiplicative.ofAdd u)) * P.compF v x))) = 0
      simp only [map_smul, htwisted, smul_zero]
    have hfactor : G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))) = 0 := by
      change lam (jacquet (P.loc v) A (μ v) f) = 0
      rw [hJ.2]
      calc
        _ = ∫ u, lam (A.ψ v (-u) •
            f ((P.loc v).w * (P.loc v).n (Multiplicative.ofAdd u))) ∂(μ v).μ :=
          (ContinuousLinearMap.integral_comp_comm lam hJ.1).symm
        _ = 0 := by rw [hfun, integral_zero]
    rw [finprod_eq_zero _ v hfactor
      (whit_finite_mulSupport P G μ Fs x (Quotient.out δ)), zero_mul]
  · have hfun : (fun u : ℂ => psiC (-u) *
        rtr (P.compC w x) (Fs.fC w) (wC * nC u)) = fun _ => (0 : ℂ) := by
      funext u
      simp only [rtr, harch, mul_zero]
    have hfactor : jacquetC (rtr (P.compC w x) (Fs.fC w)) = 0 := by
      rw [jacquetC, hfun, integral_zero]
    have hprod : (∏ w, jacquetC (rtr (P.compC w x) (Fs.fC w))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ w) hfactor
    rw [hprod, mul_zero]

/-- Weighted local ideal-coset sums give the Fourier integral at a rational frequency. -/
theorem whit_local_bruhat_coset_hasSum
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (Fs : GlobalSection P G s) (r : P.RP)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC
        (h * ((P.q r)⁻¹ * nFin P ξ * P.q r)) = scalarOf P G Fs.f Fs.fC h)
    (hΦ : ∃ g : P.tc.G, scalarOf P G Fs.f Fs.fC g ≠ 0)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
      psiInf (ν : F) (infEmbA ξ) = 1)
    (v : FinPlace F) (u : (v.adicCompletion F)ˣ) :
    let Hfn : v.adicCompletion F → ℂ := fun y =>
      A.ψ v (-((toLoc v ν : v.adicCompletion F) * y)) *
        G.lam v (Fs.f v ((P.loc v).a u * (P.loc v).w *
          (P.loc v).n (Multiplicative.ofAdd y) * P.compF v r))
    HasSum
      (fun η : (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v =>
        ((qv v) ^ (-FractionalIdeal.count F v 𝔞) : ℝ) • Hfn (Quotient.out η))
      (((absFin v u : ℂ) ^ ((1 : ℂ) / 2 + s)) *
        ((absFin v (toLoc v ν) : ℂ) ^ (s - (1 : ℂ) / 2)) *
          G.lam v ((G.T v).σa u ((G.T v).σa (toLoc v ν)
            (jacquet (P.loc v) A (μ v)
              (rtr ((P.loc v).a (toLoc v ν) * P.compF v r) (Fs.f v)))))) ∧
    HasSum
      (fun η : (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v =>
        (qv v) ^ (-FractionalIdeal.count F v 𝔞) * ‖Hfn (Quotient.out η)‖)
      (∫ y, ‖Hfn y‖ ∂(μ v).μ) := by
  classical
  let b : (v.adicCompletion F)ˣ := toLoc v ν
  let Hfn : v.adicCompletion F → ℂ := fun y =>
    A.ψ v (-((b : v.adicCompletion F) * y)) *
      G.lam v (Fs.f v ((P.loc v).a u * (P.loc v).w *
        (P.loc v).n (Multiplicative.ofAdd y) * P.compF v r))
  let F0 : v.adicCompletion F → (G.T v).V := fun y =>
    A.ψ v (-((b : v.adicCompletion F) * y)) •
      Fs.f v ((P.loc v).w * (P.loc v).n (Multiplicative.ofAdd y) * P.compF v r)
  let lamU : (G.T v).V →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap ((G.lam v).comp ((G.T v).σa u))
  let c : ℂ := (absFin v u : ℂ) ^ ((1 : ℂ) / 2 + s)
  let d : ℂ := (absFin v b : ℂ) ^ (s - (1 : ℂ) / 2)
  change HasSum
      (fun η : (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v =>
        ((qv v) ^ (-FractionalIdeal.count F v 𝔞) : ℝ) • Hfn (Quotient.out η))
      (c * d * lamU ((G.T v).σa b (jacquet (P.loc v) A (μ v)
        (rtr ((P.loc v).a b * P.compF v r) (Fs.f v))))) ∧
    HasSum
      (fun η : (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v =>
        (qv v) ^ (-FractionalIdeal.count F v 𝔞) * ‖Hfn (Quotient.out η)‖)
      (∫ y, ‖Hfn y‖ ∂(μ v).μ)
  have hFourier := whit_local_fourier_dilation (P.loc v) (G.T v) A (μ v) hs
    (Fs.f v) (Fs.f_sec v) b (P.compF v r)
  have hF0 : Integrable F0 (μ v).μ := hFourier.1
  have hpoint (y : v.adicCompletion F) : Hfn y = c * lamU (F0 y) := by
    have hvec := (Fs.f_sec v).1 0 u
      ((P.loc v).w * (P.loc v).n (Multiplicative.ofAdd y) * P.compF v r)
    have hscalar : G.lam v (Fs.f v ((P.loc v).a u * (P.loc v).w *
        (P.loc v).n (Multiplicative.ofAdd y) * P.compF v r)) =
          c * lamU (Fs.f v ((P.loc v).w *
            (P.loc v).n (Multiplicative.ofAdd y) * P.compF v r)) := by
      simpa [c, lamU, mul_assoc] using congrArg (G.lam v) hvec
    dsimp only [Hfn, F0]
    rw [hscalar, map_smul, smul_eq_mul]
    ring
  have hH : Hfn = fun y => c * lamU (F0 y) := funext hpoint
  have hint : Integrable Hfn (μ v).μ := by
    rw [hH]
    exact (lamU.integrable_comp hF0).const_mul c
  have hperiod (x y : v.adicCompletion F) (hy : y ∈ idealLocalPeriods 𝔞 v) :
      Hfn (x + y) = Hfn x := by
    have hψy : A.ψ v (-((b : v.adicCompletion F) * y)) = 1 :=
      whit_local_ideal_character D A 𝔞 h𝔞 ν hν v y hy
    have harg : -((b : v.adicCompletion F) * (x + y)) =
        -((b : v.adicCompletion F) * x) + -((b : v.adicCompletion F) * y) := by ring
    have hψ : A.ψ v (-((b : v.adicCompletion F) * (x + y))) =
        A.ψ v (-((b : v.adicCompletion F) * x)) := by
      rw [harg, (A.ψ v).map_add_eq_mul, hψy, mul_one]
    have hn : (P.loc v).n (Multiplicative.ofAdd (x + y)) =
        (P.loc v).n (Multiplicative.ofAdd x) * (P.loc v).n (Multiplicative.ofAdd y) := by
      rw [ofAdd_add, map_mul]
    have hp := local_scalar_ideal_periods_of_nonzero P G Fs r 𝔞 h𝔞 hfix hΦ v
      ((P.loc v).a u * (P.loc v).w * (P.loc v).n (Multiplicative.ofAdd x)) y hy
    have hscalar : G.lam v (Fs.f v ((P.loc v).a u * (P.loc v).w *
        (P.loc v).n (Multiplicative.ofAdd (x + y)) * P.compF v r)) =
          G.lam v (Fs.f v ((P.loc v).a u * (P.loc v).w *
            (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r)) := by
      rw [hn]
      simpa only [mul_assoc] using hp
    dsimp only [Hfn]
    rw [hψ, hscalar]
  obtain ⟨hsum, hnorm⟩ := idealLocalPeriods_integral_cosets 𝔞 v (μ v) Hfn hint hperiod
  have hFint : (∫ y, F0 y ∂(μ v).μ) =
      d • (G.T v).σa b (jacquet (P.loc v) A (μ v)
        (rtr ((P.loc v).a b * P.compF v r) (Fs.f v))) := hFourier.2
  have hIntegral : (∫ y, Hfn y ∂(μ v).μ) =
      c * d * lamU ((G.T v).σa b (jacquet (P.loc v) A (μ v)
        (rtr ((P.loc v).a b * P.compF v r) (Fs.f v)))) := by
    rw [hH, integral_const_mul, ContinuousLinearMap.integral_comp_comm lamU hF0,
      hFint, map_smul, smul_eq_mul, mul_assoc]
  rw [hIntegral] at hsum
  exact ⟨hsum, hnorm⟩

/-- The weighted rational ideal quotient reindexes as the direct sum of local quotients. -/
theorem whit_bruhat_ideal_quotient_reindex
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (r : P.RP)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC
        (h * ((P.q r)⁻¹ * nFin P ξ * P.q r)) = scalarOf P G Fs.f Fs.fC h)
    (hΦ : ∃ g : P.tc.G, scalarOf P G Fs.f Fs.fC g ≠ 0)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
      psiInf (ν : F) (infEmbA ξ) = 1) (δ : Fˣ) :
    let Hfn : ∀ v : FinPlace F, v.adicCompletion F → ℂ := fun v y =>
      A.ψ v (-((toLoc v ν : v.adicCompletion F) * y)) *
        G.lam v (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
          (P.loc v).n (Multiplicative.ofAdd y) * P.compF v r))
    let Q := fun v : FinPlace F => (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v
    let Lfn : ∀ v : FinPlace F, Q v → ℂ := fun v η => Hfn v (Quotient.out η)
    (∃ T : Finset (FinPlace F), ∀ v ∉ T, Lfn v 0 = 1) ∧
    (∑' η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup,
      ∏ᶠ v, Hfn v (algebraMap F (v.adicCompletion F) (Quotient.out η))) =
      (∑' a : Π₀ v : FinPlace F, Q v, ∏ᶠ v, Lfn v (a v)) ∧
    (Summable (fun η : F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup =>
      ‖∏ᶠ v, Hfn v (algebraMap F (v.adicCompletion F) (Quotient.out η))‖) ↔
      Summable (fun a : Π₀ v : FinPlace F, Q v => ‖∏ᶠ v, Lfn v (a v)‖)) := by
  classical
  let Hfn : ∀ v : FinPlace F, v.adicCompletion F → ℂ := fun v y =>
    A.ψ v (-((toLoc v ν : v.adicCompletion F) * y)) *
      G.lam v (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
        (P.loc v).n (Multiplicative.ofAdd y) * P.compF v r))
  let Q := fun v : FinPlace F => (v.adicCompletion F) ⧸ idealLocalPeriods 𝔞 v
  let Lfn : ∀ v : FinPlace F, Q v → ℂ := fun v η => Hfn v (Quotient.out η)
  let J := F ⧸ (𝔞 : Submodule (𝓞 F) F).toAddSubgroup
  let M := Π₀ v : FinPlace F, Q v
  let f (η : J) : ℂ := ∏ᶠ v, Hfn v (algebraMap F (v.adicCompletion F) (Quotient.out η))
  let k (a : M) : ℂ := ∏ᶠ v, Lfn v (a v)
  change (∃ T : Finset (FinPlace F), ∀ v ∉ T, Lfn v 0 = 1) ∧
    (∑' η : J, f η) = (∑' a : M, k a) ∧
    (Summable (fun η : J => ‖f η‖) ↔ Summable (fun a : M => ‖k a‖))
  have hperiod (v : FinPlace F) (x y : v.adicCompletion F)
      (hy : y ∈ idealLocalPeriods 𝔞 v) : Hfn v (x + y) = Hfn v x := by
    have harg : -((toLoc v ν : v.adicCompletion F) * (x + y)) =
        -((toLoc v ν : v.adicCompletion F) * x) +
          -((toLoc v ν : v.adicCompletion F) * y) := by ring
    have hψ : A.ψ v (-((toLoc v ν : v.adicCompletion F) * (x + y))) =
        A.ψ v (-((toLoc v ν : v.adicCompletion F) * x)) := by
      rw [harg, (A.ψ v).map_add_eq_mul,
        whit_local_ideal_character D A 𝔞 h𝔞 ν hν v y hy, mul_one]
    have hscalar : G.lam v (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
        (P.loc v).n (Multiplicative.ofAdd (x + y)) * P.compF v r)) =
          G.lam v (Fs.f v ((P.loc v).a (toLoc v δ) * (P.loc v).w *
            (P.loc v).n (Multiplicative.ofAdd x) * P.compF v r)) := by
      simpa only [ofAdd_add, map_mul, mul_assoc] using
        local_scalar_ideal_periods_of_nonzero P G Fs r 𝔞 h𝔞 hfix hΦ v
          ((P.loc v).a (toLoc v δ) * (P.loc v).w *
            (P.loc v).n (Multiplicative.ofAdd x)) y hy
    dsimp only [Hfn]
    rw [hψ, hscalar]
  have hout0 (v : FinPlace F) :
      Quotient.out (0 : Q v) ∈ idealLocalPeriods 𝔞 v := by
    have hc : (QuotientAddGroup.mk (Quotient.out (0 : Q v)) : Q v) =
        QuotientAddGroup.mk (0 : v.adicCompletion F) :=
      (QuotientAddGroup.out_eq' (0 : Q v)).trans (by simp)
    simpa only [sub_zero] using QuotientAddGroup.eq_iff_sub_mem.mp hc
  have hψzero (v : FinPlace F) :
      A.ψ v (-((toLoc v ν : v.adicCompletion F) * Quotient.out (0 : Q v))) = 1 :=
    whit_local_ideal_character D A 𝔞 h𝔞 ν hν v _ (hout0 v)
  obtain ⟨T, hbase⟩ := (bruhat_ideal_quotient_reindex P G Fs r 𝔞 h𝔞 hfix hΦ δ).1
  obtain ⟨E, hE⟩ := ideal_additive_quotient_equiv 𝔞 h𝔞
  have hclass (η : J) (v : FinPlace F) :
      (QuotientAddGroup.mk (algebraMap F (v.adicCompletion F) (Quotient.out η)) : Q v) =
        E η v := by
    calc
      _ = E (QuotientAddGroup.mk (Quotient.out η)) v := (hE (Quotient.out η) v).symm
      _ = E η v := by rw [QuotientAddGroup.out_eq']
  have hterm (η : J) (v : FinPlace F) :
      Hfn v (algebraMap F (v.adicCompletion F) (Quotient.out η)) = Lfn v (E η v) := by
    let x := algebraMap F (v.adicCompletion F) (Quotient.out η)
    let y := Quotient.out (E η v)
    have hm : x - y ∈ idealLocalPeriods 𝔞 v :=
      QuotientAddGroup.eq_iff_sub_mem.mp
        ((hclass η v).trans (QuotientAddGroup.out_eq' (E η v)).symm)
    change Hfn v x = Hfn v y
    have hxy : x = y + (x - y) := by abel
    rw [hxy]
    exact hperiod v y (x - y) hm
  have hprod (η : J) : f η = k (E η) := by
    dsimp only [f, k]
    exact finprod_congr (hterm η)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨T, ?_⟩
    intro v hv
    dsimp only [Lfn, Hfn]
    rw [hψzero, one_mul]
    exact hbase v hv
  · calc
      (∑' η : J, f η) = ∑' η : J, k (E η) := tsum_congr hprod
      _ = ∑' a : M, k a := E.toEquiv.tsum_eq k
  · constructor
    · intro hf
      have hh := hf.comp_injective E.symm.injective
      exact hh.congr fun a => by
        change ‖f (E.symm a)‖ = ‖k a‖
        rw [hprod, E.apply_symm_apply]
    · intro hk
      have hh := hk.comp_injective E.injective
      exact hh.congr fun η => by
        change ‖k (E η)‖ = ‖f η‖
        rw [hprod]

/-- Period tiling and local Fourier integrals evaluate the weighted big-cell sum. -/
theorem whit_bigCell_jacquet (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (B : Set (InfinitePlace F → ℂ)) (hB : MeasurableSet B) (hBc : IsCompact (closure B))
    (hBd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) B volume)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1)
    (x : P.RP) (hx : P.q x = P.tc.rat (diagGL ν) * g) :
    ((volume B).toReal)⁻¹ * ∑' p : (Fˣ ⧸ G.Δ) × F, ∫ u in B,
      scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL (Quotient.out p.1) * weylGL * upperGL p.2) * nInf P u * g) *
          psiInf (-(ν : F)) u =
      (κF F)⁻¹ * ∑' δ, whitLiftTerm P G μ Fs x δ := by
  classical
  by_cases hΦ : ∃ h : P.tc.G, scalarOf P G Fs.f Fs.fC h ≠ 0
  · sorry
  · have hzero : ∀ h : P.tc.G, scalarOf P G Fs.f Fs.fC h = 0 := by
      push_neg at hΦ
      exact hΦ
    have hW (δ : Fˣ ⧸ G.Δ) : whitLiftTerm P G μ Fs x δ = 0 :=
      whitLiftTerm_eq_zero_of_scalarOf_eq_zero P G μ hs Fs hzero x δ
    simp only [hzero, zero_mul, integral_zero, tsum_zero, mul_zero, hW]

/-- The small cell vanishes and the big cell tiles the archimedean integral. -/
theorem whit_unfold_integral (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1)
    (x : P.RP) (hx : P.q x = P.tc.rat (diagGL ν) * g) :
    torusCoeff P (eisenstein P G Fs) g Pd (ν : F) =
      (κF F)⁻¹ * ∑' δ, whitLiftTerm P G μ Fs x δ := by
  obtain ⟨B, hB, hBc, hBd, hsplit⟩ :=
    whit_weighted_bruhat P G hs Fs g 𝔞 h𝔞 hfix Pd hPd ν hν
  exact hsplit.trans (whit_bigCell_jacquet P G μ hs Fs g 𝔞 h𝔞 hfix B hB hBc hBd ν hν x hx)

/-- **eis:whittaker** (unfolding): the `ν`-th torus coefficient is `W_E(a(ν) g)`, for `ν` in the dual
lattice. -/
theorem eisenstein_whittaker (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s)
    (g : P.tc.G) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (h𝔞 : 𝔞 ≠ 0)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G Fs.f Fs.fC h)
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
      Pd volume)
    (ν : Fˣ) (hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (ν : F) (infEmbA ξ) = 1) :
    torusCoeff P (eisenstein P G Fs) g Pd (ν : F) =
      whittakerE P G μ Fs (P.tc.rat (diagGL ν) * g) := by
  obtain ⟨x, hx⟩ := P.q_surj (P.tc.rat (diagGL ν) * g)
  rw [← hx, whit_atLift P G μ hs Fs x]
  exact whit_unfold_integral P G μ hs Fs g 𝔞 h𝔞 hfix Pd hPd ν hν x hx

/-- Local scalar translation factors pass through the convergent Whittaker series. -/
theorem whit_translate_scalar (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (y x : P.RP)
    (cf : FinPlace F → ℂ) (hcf : (Function.mulSupport cf).Finite)
    (cC : InfinitePlace F → ℂ)
    (hF : ∀ v, jacquet (P.loc v) A (μ v)
      (rtr (P.compF v y) (rtr (P.compF v x) (Fs.f v))) =
      cf v • jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))
    (hC : ∀ w, jacquetC (rtr (P.compC w y) (rtr (P.compC w x) (Fs.fC w))) =
      cC w * jacquetC (rtr (P.compC w x) (Fs.fC w))) :
    whittakerE P G μ Fs (P.q (y * x)) =
      ((∏ᶠ v, cf v) * ∏ w, cC w) * whittakerE P G μ Fs (P.q x) := by
  classical
  have htrF (v : FinPlace F) :
      rtr (P.compF v (y * x)) (Fs.f v) =
        rtr (P.compF v y) (rtr (P.compF v x) (Fs.f v)) := by
    funext h
    simp only [rtr, map_mul, mul_assoc]
  have htrC (w : InfinitePlace F) :
      rtr (P.compC w (y * x)) (Fs.fC w) =
        rtr (P.compC w y) (rtr (P.compC w x) (Fs.fC w)) := by
    funext h
    simp only [rtr, map_mul, mul_assoc]
  have hlocal (δ : Fˣ ⧸ G.Δ) (v : FinPlace F) :
      G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v (y * x)) (Fs.f v)))) =
      cf v * G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)))) := by
    rw [htrF v, hF v]
    simp only [map_smul, smul_eq_mul]
  have hcomplex (w : InfinitePlace F) :
      jacquetC (rtr (P.compC w (y * x)) (Fs.fC w)) =
        cC w * jacquetC (rtr (P.compC w x) (Fs.fC w)) := by
    rw [htrC w, hC w]
  have hterm (δ : Fˣ ⧸ G.Δ) :
      whitLiftTerm P G μ Fs (y * x) δ =
        ((∏ᶠ v, cf v) * ∏ w, cC w) * whitLiftTerm P G μ Fs x δ := by
    unfold whitLiftTerm
    simp_rw [hlocal δ, hcomplex]
    rw [finprod_mul_distrib hcf
      (whit_finite_mulSupport P G μ Fs x (Quotient.out δ)), Finset.prod_mul_distrib]
    ac_rfl
  have hsum := (whitLiftTerm_summable P G μ hs Fs x).of_norm
  rw [whit_atLift P G μ hs Fs (y * x), whit_atLift P G μ hs Fs x]
  simp_rw [hterm]
  rw [hsum.tsum_mul_left ((∏ᶠ v, cf v) * ∏ w, cC w)]
  ac_rfl

/-- Genuineness follows by inserting the center into one local component. -/
theorem whit_center (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (ζ : rootsOfUnity 3 ℂ) (g : P.tc.G) :
    whittakerE P G μ Fs (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * whittakerE P G μ Fs g := by
  classical
  obtain ⟨I, hI, hImax⟩ :=
    Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField F)
  let v : FinPlace F := ⟨I, hImax.isPrime, hI⟩
  obtain ⟨x, hx⟩ := P.q_surj g
  let y : P.RP := P.incl v ((P.loc v).z ζ)
  let cf : FinPlace F → ℂ := fun w => if w = v then ((ζ : ℂˣ) : ℂ) else 1
  have hcf : (Function.mulSupport cf).Finite := by
    refine (Set.finite_singleton v).subset ?_
    intro w hw
    change w = v
    by_contra hwv
    exact hw (by simp only [cf, if_neg hwv])
  have hprod : (∏ᶠ w, cf w) = ((ζ : ℂˣ) : ℂ) := by
    calc
      (∏ᶠ w, cf w) = cf v := finprod_eq_single cf v (by
        intro w hw
        simp only [cf, if_neg hw])
      _ = ((ζ : ℂˣ) : ℂ) := by simp only [cf, if_pos rfl]
  have hlocal (w : FinPlace F) :
      jacquet (P.loc w) A (μ w)
        (rtr (P.compF w y) (rtr (P.compF w x) (Fs.f w))) =
      cf w • jacquet (P.loc w) A (μ w) (rtr (P.compF w x) (Fs.f w)) := by
    by_cases hw : w = v
    · subst w
      dsimp only [y]
      rw [P.incl_compF]
      simpa only [cf, if_pos rfl] using
        (jacquet_equiv (P.loc v) (G.T v) A (μ v) s
          (rtr (P.compF v x) (Fs.f v)) ((Fs.f_sec v).rtr (P.compF v x))).2 ζ
    · have hother : P.compF w y = 1 :=
        P.incl_compF_other v w (Ne.symm hw) ((P.loc v).z ζ)
      rw [hother]
      simp only [cf, if_neg hw, one_smul]
      apply congrArg (jacquet (P.loc w) A (μ w))
      funext h
      simp only [rtr, mul_one]
  have hcomplex (w : InfinitePlace F) :
      jacquetC (rtr (P.compC w y) (rtr (P.compC w x) (Fs.fC w))) =
      (1 : ℂ) * jacquetC (rtr (P.compC w x) (Fs.fC w)) := by
    have hcomp : P.compC w y = 1 := P.incl_compC v ((P.loc v).z ζ) w
    rw [hcomp, one_mul]
    apply congrArg jacquetC
    funext h
    simp only [rtr, mul_one]
  have hW := whit_translate_scalar P G μ hs Fs y x cf hcf (fun _ => 1) hlocal hcomplex
  have hy : P.q y = P.tc.z ζ := (P.q_incl v ((P.loc v).z ζ)).trans (P.emb_z v ζ)
  have hqx : P.q (y * x) = P.tc.z ζ * g := by rw [map_mul, hy, hx]
  rw [hqx, hprod, hx] at hW
  simpa only [Finset.prod_const_one, mul_one] using hW

theorem whit_unipotentS (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (u : S.FS) (g : P.tc.G) :
    whittakerE P G μ Fs (P.tc.nS (Multiplicative.ofAdd u) * g) =
      S.e A u * whittakerE P G μ Fs g := by
  classical
  obtain ⟨x, hx⟩ := P.q_surj g
  obtain ⟨y, hy, hFy, hCy⟩ := P.nS_components u
  let cf : FinPlace F → ℂ := fun v =>
    if hv : v ∈ S.Sf then A.ψ v (u.1 ⟨v, hv⟩) else 1
  have hsupport : Function.mulSupport cf ⊆ (S.Sf : Set (FinPlace F)) := by
    intro v hv
    change v ∈ S.Sf
    by_contra hvS
    exact hv (by simp only [cf, dif_neg hvS])
  have hcf : (Function.mulSupport cf).Finite := S.Sf.finite_toSet.subset hsupport
  have hprod : (∏ᶠ v, cf v) = ∏ v : S.Sf, A.ψ v.1 (u.1 v) := by
    rw [finprod_eq_prod_of_mulSupport_subset cf hsupport,
      ← Finset.prod_coe_sort S.Sf cf]
    apply Finset.prod_congr rfl
    intro v _
    simp only [cf, dif_pos v.property]
  have hlocal (v : FinPlace F) :
      jacquet (P.loc v) A (μ v)
        (rtr (P.compF v y) (rtr (P.compF v x) (Fs.f v))) =
      cf v • jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs.f v)) := by
    by_cases hv : v ∈ S.Sf
    · rw [hFy v, dif_pos hv]
      simpa only [cf, dif_pos hv] using
        (jacquet_equiv (P.loc v) (G.T v) A (μ v) s
          (rtr (P.compF v x) (Fs.f v)) ((Fs.f_sec v).rtr (P.compF v x))).1
            (u.1 ⟨v, hv⟩)
    · rw [hFy v, dif_neg hv]
      simp only [cf, dif_neg hv, one_smul]
      apply congrArg (jacquet (P.loc v) A (μ v))
      funext h
      simp only [rtr, mul_one]
  have hs0 : 0 < s.re := by linarith only [hs]
  have hcomplex (w : InfinitePlace F) :
      jacquetC (rtr (P.compC w y) (rtr (P.compC w x) (Fs.fC w))) =
      psiC (u.2 w) * jacquetC (rtr (P.compC w x) (Fs.fC w)) := by
    have hf : IsSectionC s (rtr (P.compC w x) (Fs.fC w)) := by
      intro t a h
      simpa only [rtr, mul_assoc] using (Fs.fC_sec w).1 t a (h * P.compC w x)
    have hcont : Continuous (rtr (P.compC w x) (Fs.fC w)) := by
      change Continuous (fun h : PGL2 ℂ => Fs.fC w (h * P.compC w x))
      exact (Fs.fC_sec w).2.comp (continuous_id.mul continuous_const)
    rw [hCy w]
    change jacquetC (rtr (nC (u.2 w)) (rtr (P.compC w x) (Fs.fC w))) = _
    exact jacquetC_equiv s hs0 (rtr (P.compC w x) (Fs.fC w)) hf hcont (u.2 w)
  have hW := whit_translate_scalar P G μ hs Fs y x cf hcf
    (fun w => psiC (u.2 w)) hlocal hcomplex
  have hqx : P.q (y * x) = P.tc.nS (Multiplicative.ofAdd u) * g := by
    rw [map_mul, hy, hx]
  rw [hqx, hprod, hx] at hW
  simpa only [SData.e] using hW

theorem whit_unipotentExterior (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (v : FinPlace F) (hv : v ∉ S.Sf)
    (u : v.adicCompletion F) (g : P.tc.G) :
    whittakerE P G μ Fs (P.tc.n v (Multiplicative.ofAdd u) * g) =
      A.ψ v u * whittakerE P G μ Fs g := by
  classical
  obtain ⟨x, hx⟩ := P.q_surj g
  let y : P.RP := P.incl v ((P.loc v).n (Multiplicative.ofAdd u))
  let cf : FinPlace F → ℂ := fun w => if w = v then A.ψ v u else 1
  have hcf : (Function.mulSupport cf).Finite := by
    refine (Set.finite_singleton v).subset ?_
    intro w hw
    change w = v
    by_contra hwv
    exact hw (by simp only [cf, if_neg hwv])
  have hprod : (∏ᶠ w, cf w) = A.ψ v u := by
    calc
      (∏ᶠ w, cf w) = cf v := finprod_eq_single cf v (by
        intro w hw
        simp only [cf, if_neg hw])
      _ = A.ψ v u := by simp only [cf, if_pos rfl]
  have hlocal (w : FinPlace F) :
      jacquet (P.loc w) A (μ w)
        (rtr (P.compF w y) (rtr (P.compF w x) (Fs.f w))) =
      cf w • jacquet (P.loc w) A (μ w) (rtr (P.compF w x) (Fs.f w)) := by
    by_cases hw : w = v
    · subst w
      dsimp only [y]
      rw [P.incl_compF]
      simpa only [cf, if_pos rfl] using
        (jacquet_equiv (P.loc v) (G.T v) A (μ v) s
          (rtr (P.compF v x) (Fs.f v)) ((Fs.f_sec v).rtr (P.compF v x))).1 u
    · have hother : P.compF w y = 1 :=
        P.incl_compF_other v w (Ne.symm hw) ((P.loc v).n (Multiplicative.ofAdd u))
      rw [hother]
      simp only [cf, if_neg hw, one_smul]
      apply congrArg (jacquet (P.loc w) A (μ w))
      funext h
      simp only [rtr, mul_one]
  have hcomplex (w : InfinitePlace F) :
      jacquetC (rtr (P.compC w y) (rtr (P.compC w x) (Fs.fC w))) =
      (1 : ℂ) * jacquetC (rtr (P.compC w x) (Fs.fC w)) := by
    have hcomp : P.compC w y = 1 :=
      P.incl_compC v ((P.loc v).n (Multiplicative.ofAdd u)) w
    rw [hcomp, one_mul]
    apply congrArg jacquetC
    funext h
    simp only [rtr, mul_one]
  have hW := whit_translate_scalar P G μ hs Fs y x cf hcf (fun _ => 1) hlocal hcomplex
  have hy : P.q y = P.tc.n v (Multiplicative.ofAdd u) :=
    (P.q_incl v ((P.loc v).n (Multiplicative.ofAdd u))).trans
      (P.emb_n v hv (Multiplicative.ofAdd u))
  have hqx : P.q (y * x) = P.tc.n v (Multiplicative.ofAdd u) * g := by
    rw [map_mul, hy, hx]
  rw [hqx, hprod, hx] at hW
  simpa only [Finset.prod_const_one, mul_one] using hW

/-- The rational finite unipotent has trivial complex components. -/
theorem whit_nFin_lift (P : CoverPackage D S H A) (ξ : F) :
    ∃ y : P.RP, P.q y = nFin P ξ ∧
      (∀ v : FinPlace F, P.compF v y =
        (P.loc v).n (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F) ξ))) ∧
      ∀ w, P.compC w y = 1 := by
  classical
  have upper_map {K : Type} [Field K] (f : F →+* K) :
      Matrix.GeneralLinearGroup.map f (upperGL ξ) = upperM K (f ξ) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.map_apply, upperGL, upperM]
  obtain ⟨z, hzq, hzF, hzC⟩ := P.nS_components
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), -(infEmbA ξ))
  refine ⟨P.ratRP (upperGL ξ) * z, ?_, ?_, ?_⟩
  · rw [map_mul, P.q_ratRP, hzq]
    rfl
  · intro v
    rw [map_mul, P.compF_ratRP, upper_map, hzF v]
    have hz : (if hv : v ∈ S.Sf then
        (P.loc v).n (Multiplicative.ofAdd
          ((0 : ∀ u : S.Sf, u.1.adicCompletion F) ⟨v, hv⟩)) else 1) = 1 := by
      split_ifs <;> simp
    rw [hz, mul_one, ← (P.loc v).sec_n]
  · intro w
    rw [map_mul, P.compC_ratRP, upper_map, hzC w]
    have hupper : upperM ℂ (w.embedding ξ) * upperM ℂ (-w.embedding ξ) = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [upperM, Matrix.mul_apply, Fin.sum_univ_two]
    change QuotientGroup.mk (upperM ℂ (w.embedding ξ)) *
      QuotientGroup.mk (upperM ℂ (-w.embedding ξ)) = (1 : PGL2 ℂ)
    rw [← QuotientGroup.mk_mul, hupper, QuotientGroup.mk_one]

/-- Smoothness at the finite places gives a nonzero integral ideal of periods. -/
theorem whit_finite_period (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G) :
    ∃ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F, 𝔞 ≠ 0 ∧
      (∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∃ a : 𝓞 F, (a : F) = ξ) ∧
      ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) =
          scalarOf P G Fs.f Fs.fC h := by
  classical
  obtain ⟨x, hx⟩ := P.q_surj g
  let bad : Set (FinPlace F) :=
    {v | ∃ hv : v ∉ S.Sf, P.compF v x ∉ (P.tame v hv).Kmax}
  have hbad : bad.Finite := P.comp_restricted x
  let E : Finset (FinPlace F) := Fs.T0 ∪ hbad.toFinset
  have hsmooth (v : E) : ∃ m, (P.loc v.1).m0 ≤ m ∧
      ∀ h, ∀ k ∈ (P.loc v.1).Kc m,
        rtr (P.compF v.1 x) (Fs.f v.1) (h * k) =
          rtr (P.compF v.1 x) (Fs.f v.1) h :=
    ((Fs.f_sec v.1).rtr (P.compF v.1 x)).2.2
  choose m hm hfix using hsmooth
  obtain ⟨I, hI, hIval⟩ := whit_small_ideal E m
  refine ⟨(I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F),
    FractionalIdeal.coeIdeal_ne_zero.mpr hI, ?_, ?_⟩
  · intro ξ hξ
    obtain ⟨a, haI, haξ⟩ :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 F))).mp hξ
    exact ⟨a, haξ⟩
  · intro ξ hξ h
    obtain ⟨a, haI, rfl⟩ :=
      (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 F))).mp hξ
    have hloc (v : FinPlace F) (u : (P.loc v).L) :
        Fs.f v (u * ((P.compF v x)⁻¹ *
          (P.loc v).n (Multiplicative.ofAdd
            (algebraMap F (v.adicCompletion F) (a : F))) * P.compF v x)) = Fs.f v u := by
      by_cases hvE : v ∈ E
      · let vE : E := ⟨v, hvE⟩
        have hball : algebraMap F (v.adicCompletion F) (a : F) ∈ ball v (m vE) := by
          change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤
            WithZero.exp (-(m vE : ℤ))
          have hval := hIval a haI vE
          change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) ≤
            WithZero.exp (-(m vE : ℤ)) at hval
          rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)] at hval
          exact hval
        have hlocal := hfix vE (u * (P.compF v x)⁻¹)
          ((P.loc v).n (Multiplicative.ofAdd
            (algebraMap F (v.adicCompletion F) (a : F))))
          ((P.loc v).n_Kc (m vE) (hm vE) _ hball)
        simpa only [vE, rtr, mul_assoc, inv_mul_cancel, mul_one] using hlocal
      · have hvT : v ∉ Fs.T0 := fun hv => hvE (Finset.mem_union.mpr (Or.inl hv))
        have hvS : v ∉ S.Sf := fun hv => hvT (Fs.sub hv)
        have hxK : P.compF v x ∈ (P.tame v hvS).Kmax := by
          by_contra hout
          apply hvE
          apply Finset.mem_union.mpr
          exact Or.inr (hbad.mem_toFinset.mpr ⟨hvS, hout⟩)
        have haint : algebraMap F (v.adicCompletion F) (a : F) ∈
            v.adicCompletionIntegers F := by
          change ((a : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
          rw [HeightOneSpectrum.mem_adicCompletionIntegers,
            v.valuedAdicCompletion_eq_valuation']
          exact v.valuation_le_one a
        have hnK := (P.tame v hvS).n_mem _ haint
        exact (Fs.f_sph v hvT).2 u _
          ((P.tame v hvS).Kmax.mul_mem
            ((P.tame v hvS).Kmax.mul_mem ((P.tame v hvS).Kmax.inv_mem hxK) hnK) hxK)
    obtain ⟨y, hy, hyF, hyC⟩ := whit_nFin_lift P (a : F)
    obtain ⟨z, hz⟩ := P.q_surj h
    have hq : P.q (z * (x⁻¹ * y * x)) = h * (g⁻¹ * nFin P (a : F) * g) := by
      simp only [map_mul, map_inv, hx, hy, hz]
    rw [← hq, ← hz]
    apply scalarOf_lift_components Fs (z * (x⁻¹ * y * x)) z
    · intro v
      simp only [map_mul, map_inv, hyF v]
      exact congrArg (G.lam v) (hloc v (P.compF v z))
    · intro w
      simp only [map_mul, map_inv, hyC w, mul_one, inv_mul_cancel, one_mul]

/-- Choose an adapted period ideal, a domain, and the dual character condition. -/
theorem whit_period_exists (P : CoverPackage D S H A) (G : GlobalDatum P)
    {s : ℂ} (Fs : GlobalSection P G s) (g : P.tc.G) :
    ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (Pd : Set (InfinitePlace F → ℂ)), 𝔞 ≠ 0 ∧
      (∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        scalarOf P G Fs.f Fs.fC (h * (g⁻¹ * nFin P ξ * g)) =
          scalarOf P G Fs.f Fs.fC h) ∧
      IsAddFundamentalDomain
        ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume ∧
      ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), psiInf (1 : F) (infEmbA ξ) = 1 := by
  obtain ⟨𝔞, h𝔞, hint, hfix⟩ := whit_finite_period P G Fs g
  obtain ⟨Pd, hPd⟩ := whit_fractional_lattice_domain D 𝔞 h𝔞
  refine ⟨𝔞, Pd, h𝔞, hfix, hPd, ?_⟩
  intro ξ hξ
  obtain ⟨a, rfl⟩ := hint ξ hξ
  simpa only [psiInf, infEmbA, map_one, one_mul, RingHom.pi_apply] using
    whit_integral_inf_character D S A a

theorem whit_rightInvariant (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (k : P.tc.G)
    (hk : ∀ h, scalarOf P G Fs.f Fs.fC (h * k) = scalarOf P G Fs.f Fs.fC h)
    (g : P.tc.G) : whittakerE P G μ Fs (g * k) = whittakerE P G μ Fs g := by
  obtain ⟨𝔞, Pd, h𝔞, hfix, hPd, hν⟩ := whit_period_exists P G Fs g
  have hkInv (h : P.tc.G) :
      scalarOf P G Fs.f Fs.fC (h * k⁻¹) = scalarOf P G Fs.f Fs.fC h := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using (hk (h * k⁻¹)).symm
  have hfixk (ξ : F) (hξ : ξ ∈ (𝔞 : Submodule (𝓞 F) F)) (h : P.tc.G) :
      scalarOf P G Fs.f Fs.fC (h * ((g * k)⁻¹ * nFin P ξ * (g * k))) =
        scalarOf P G Fs.f Fs.fC h := by
    calc
      _ = scalarOf P G Fs.f Fs.fC
          (((h * k⁻¹) * (g⁻¹ * nFin P ξ * g)) * k) := by congr 1; group
      _ = scalarOf P G Fs.f Fs.fC ((h * k⁻¹) * (g⁻¹ * nFin P ξ * g)) := hk _
      _ = scalarOf P G Fs.f Fs.fC (h * k⁻¹) := hfix ξ hξ _
      _ = scalarOf P G Fs.f Fs.fC h := hkInv h
  have hdiag : diagGL (1 : Fˣ) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL, Matrix.one_apply]
  have hwg := eisenstein_whittaker P G μ hs Fs g 𝔞 h𝔞 hfix Pd hPd (1 : Fˣ) hν
  have hwgk := eisenstein_whittaker P G μ hs Fs (g * k) 𝔞 h𝔞 hfixk Pd hPd (1 : Fˣ) hν
  rw [hdiag, map_one, one_mul] at hwg hwgk
  have hE := (eisenstein_automorphic P G hs Fs).2.2 k hk
  have htorus : torusCoeff P (eisenstein P G Fs) (g * k) Pd (1 : F) =
      torusCoeff P (eisenstein P G Fs) g Pd (1 : F) := by
    unfold torusCoeff
    congr 1
    apply congrArg (fun f : (InfinitePlace F → ℂ) → ℂ => ∫ x in Pd, f x)
    funext x
    rw [show nInf P x * (g * k) = (nInf P x * g) * k by simp only [mul_assoc], hE]
  exact hwgk.symm.trans (htorus.trans hwg)

/-- **eis:whittaker-equiv**: `W_E` is genuine, `(N(F_S), e)`- and `(N(K_v), ψ_v)`-equivariant,
right-invariant like the sections, and vanishes at `a(ν)g` for `ν` outside the dual lattice. -/
theorem whittakerE_equiv (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) :
    (∀ ζ g, whittakerE P G μ Fs (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * whittakerE P G μ Fs g) ∧
    (∀ x g, whittakerE P G μ Fs (P.tc.nS (Multiplicative.ofAdd x) * g) =
      S.e A x * whittakerE P G μ Fs g) ∧
    (∀ v, v ∉ S.Sf → ∀ x g, whittakerE P G μ Fs (P.tc.n v (Multiplicative.ofAdd x) * g) =
      A.ψ v x * whittakerE P G μ Fs g) ∧
    (∀ k : P.tc.G, (∀ h, scalarOf P G Fs.f Fs.fC (h * k) = scalarOf P G Fs.f Fs.fC h) →
      ∀ g, whittakerE P G μ Fs (g * k) = whittakerE P G μ Fs g) := by
  exact ⟨whit_center P G μ hs Fs, whit_unipotentS P G μ hs Fs,
    whit_unipotentExterior P G μ hs Fs, whit_rightInvariant P G μ hs Fs⟩

/-- The exterior Jacquet product, which stays fixed as the S-part varies. -/
def whitExteriorTerm (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s)
    (x0 : P.RP) (δ : Fˣ ⧸ G.Δ) : ℂ :=
  ∏ᶠ v : {v : FinPlace F // v ∉ S.Sf}, G.lam v.1 ((G.T v.1).σa
    (toLoc v.1 (Quotient.out δ))
    (jacquet (P.loc v.1) A (μ v.1) (rtr (P.compF v.1 x0) (Fs.f v.1))))

def whitTensorTerm (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s)
    (x0 : P.RP) (z : ∀ v : S.Sf, (G.T v.1).V) (δ : Fˣ ⧸ G.Δ) : ℂ :=
  whitExteriorTerm P G μ Fs x0 δ *
    ∏ v : S.Sf, G.lam v.1 ((G.T v.1).σa (toLoc v.1 (Quotient.out δ)) (z v))

/-- Summability on basis tensors extends to every tensor in the finite dimensional S-part. -/
theorem whitTensorTerm_summable (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x0 : P.RP) (z : ∀ v : S.Sf, (G.T v.1).V) :
    Summable (fun δ : Fˣ ⧸ G.Δ => ‖whitTensorTerm P G μ Fs x0 z δ‖) := by
  let E := Fs.T0 ∪ (P.comp_restricted x0).toFinset
  have hE : Fs.T0 ⊆ E := Finset.subset_union_left
  have hcomp (v : FinPlace F) (hv : v ∉ E) :
      P.compF v x0 ∈ (P.tame v (fun h => hv (hE (Fs.sub h)))).Kmax := by
    by_contra hk
    apply hv
    apply Finset.mem_union_right
    exact (P.comp_restricted x0).mem_toFinset.mpr
      ⟨(fun h => hv (hE (Fs.sub h))), hk⟩
  let w (v : FinPlace F) : (G.T v).V :=
    if hv : v ∈ S.Sf then z ⟨v, hv⟩
    else jacquet (P.loc v) A (μ v) (rtr (P.compF v x0) (Fs.f v))
  have hw (v : FinPlace F) (hv : v ∉ E) : w v =
      jacquet (P.loc v) A (μ v) (rtr (P.compF v x0) (Fs.f v)) := by
    have hvS : v ∉ S.Sf := fun h => hv (hE (Fs.sub h))
    simp only [w, dif_neg hvS]
  have hsum := whit_jacquet_family_summable P G μ hs Fs x0 E hE hcomp w hw
  let a (δ : Fˣ ⧸ G.Δ) (v : FinPlace F) : ℂ :=
    G.lam v ((G.T v).σa (toLoc v (Quotient.out δ)) (w v))
  have hfin (δ : Fˣ ⧸ G.Δ) : (Function.mulSupport (a δ)).Finite := by
    refine (S.Sf.finite_toSet.union
      (whit_finite_mulSupport P G μ Fs x0 (Quotient.out δ))).subset ?_
    intro v hv
    by_cases hvS : v ∈ S.Sf
    · exact Or.inl hvS
    · refine Or.inr ?_
      change G.lam v ((G.T v).σa (toLoc v (Quotient.out δ)) (w v)) ≠ 1 at hv
      change G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
        (jacquet (P.loc v) A (μ v) (rtr (P.compF v x0) (Fs.f v)))) ≠ 1
      simpa only [w, dif_neg hvS] using hv
  have heq (δ : Fˣ ⧸ G.Δ) : (∏ᶠ v, a δ v) = whitTensorTerm P G μ Fs x0 z δ := by
    have hsplit := finprod_mem_union' (f := a δ)
      (show Disjoint (S.Sf : Set (FinPlace F)) (S.Sf : Set (FinPlace F))ᶜ
        from disjoint_compl_right)
      ((hfin δ).subset (fun _ hv => hv.2))
      ((hfin δ).subset (fun _ hv => hv.2))
    simp only [Set.union_compl_self, finprod_mem_univ] at hsplit
    rw [← finprod_set_coe_eq_finprod_mem (S.Sf : Set (FinPlace F)),
      ← finprod_set_coe_eq_finprod_mem (S.Sf : Set (FinPlace F))ᶜ] at hsplit
    change (∏ᶠ v, a δ v) = (∏ᶠ v : S.Sf, a δ v.1) *
      (∏ᶠ v : {v : FinPlace F // v ∉ S.Sf}, a δ v.1) at hsplit
    rw [finprod_eq_prod_of_fintype (fun v : S.Sf => a δ v.1)] at hsplit
    have hS : (∏ v : S.Sf, a δ v.1) =
        ∏ v : S.Sf, G.lam v.1 ((G.T v.1).σa (toLoc v.1 (Quotient.out δ)) (z v)) := by
      apply Finset.prod_congr rfl
      intro v _
      simp only [a, w, dif_pos v.property]
    have hExt : (∏ᶠ v : {v : FinPlace F // v ∉ S.Sf}, a δ v.1) =
        whitExteriorTerm P G μ Fs x0 δ := by
      unfold whitExteriorTerm
      apply finprod_congr
      intro v
      simp only [a, w, dif_neg v.property]
    rw [hS, hExt] at hsplit
    simpa only [whitTensorTerm, mul_comm] using hsplit
  change Summable (fun δ : Fˣ ⧸ G.Δ => ‖∏ᶠ v, a δ v‖) at hsum
  exact hsum.congr (fun δ => congrArg norm (heq δ))

/-- The summable delta-series defines a multilinear form by tsum_add and tsum_smul. -/
theorem whit_tensor_multilinear (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x0 : P.RP) :
    ∃ Λ : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ,
      ∀ z, Λ z = (κF F)⁻¹ * ∑' δ, whitTensorTerm P G μ Fs x0 z δ := by
  let term (δ : Fˣ ⧸ G.Δ) :
      MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ :=
    whitExteriorTerm P G μ Fs x0 δ •
      (MultilinearMap.mkPiAlgebra ℂ S.Sf ℂ).compLinearMap
        (fun v => (G.lam v.1).comp
          ((G.T v.1).σa (toLoc v.1 (Quotient.out δ))))
  have hterm (δ : Fˣ ⧸ G.Δ) (z : ∀ v : S.Sf, (G.T v.1).V) :
      term δ z = whitTensorTerm P G μ Fs x0 z δ := by
    rfl
  have hsum (z : ∀ v : S.Sf, (G.T v.1).V) : Summable (fun δ => term δ z) := by
    simpa only [hterm] using (whitTensorTerm_summable P G μ hs Fs x0 z).of_norm
  let Λ0 : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ :=
    { toFun := fun z => ∑' δ, term δ z
      map_update_add' := by
        intro _ z v x y
        simp_rw [MultilinearMap.map_update_add]
        exact (hsum (Function.update z v x)).tsum_add (hsum (Function.update z v y))
      map_update_smul' := by
        intro _ z v c x
        simp_rw [MultilinearMap.map_update_smul]
        exact (hsum (Function.update z v x)).tsum_const_smul c }
  refine ⟨(κF F)⁻¹ • Λ0, ?_⟩
  intro z
  change (κF F)⁻¹ * (∑' δ, term δ z) =
    (κF F)⁻¹ * ∑' δ, whitTensorTerm P G μ Fs x0 z δ
  simp_rw [hterm]

/-- Separate the finite S-product and the fixed exterior product at a common lift. -/
theorem whit_tensor_formula (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 1 / 2 < s.re)
    (Fs : GlobalSection P G s) (x0 : P.RP) (Fs' : GlobalSection P G s) (x : P.RP)
    (hext : ∀ v, v ∉ S.Sf → Fs'.f v = Fs.f v) (hC : Fs'.fC = Fs.fC)
    (hx : ∀ v, v ∉ S.Sf → P.compF v x = P.compF v x0) :
    whittakerE P G μ Fs' (P.q x) =
      ((κF F)⁻¹ * ∑' δ, whitTensorTerm P G μ Fs x0
        (fun v => jacquet (P.loc v.1) A (μ v.1) (rtr (P.compF v.1 x) (Fs'.f v.1))) δ) *
      ∏ w, jacquetC (rtr (P.compC w x) (Fs'.fC w)) := by
  let z (v : S.Sf) : (G.T v.1).V :=
    jacquet (P.loc v.1) A (μ v.1) (rtr (P.compF v.1 x) (Fs'.f v.1))
  let a (δ : Fˣ ⧸ G.Δ) (v : FinPlace F) : ℂ :=
    G.lam v ((G.T v).σa (toLoc v (Quotient.out δ))
      (jacquet (P.loc v) A (μ v) (rtr (P.compF v x) (Fs'.f v))))
  let C := ∏ w, jacquetC (rtr (P.compC w x) (Fs'.fC w))
  have hprod (δ : Fˣ ⧸ G.Δ) : (∏ᶠ v, a δ v) = whitTensorTerm P G μ Fs x0 z δ := by
    have hfin : (Function.mulSupport (a δ)).Finite :=
      whit_finite_mulSupport P G μ Fs' x (Quotient.out δ)
    have hsplit := finprod_mem_union' (f := a δ)
      (show Disjoint (S.Sf : Set (FinPlace F)) (S.Sf : Set (FinPlace F))ᶜ
        from disjoint_compl_right)
      (hfin.subset (fun _ hv => hv.2)) (hfin.subset (fun _ hv => hv.2))
    simp only [Set.union_compl_self, finprod_mem_univ] at hsplit
    rw [← finprod_set_coe_eq_finprod_mem (S.Sf : Set (FinPlace F)),
      ← finprod_set_coe_eq_finprod_mem (S.Sf : Set (FinPlace F))ᶜ] at hsplit
    change (∏ᶠ v, a δ v) = (∏ᶠ v : S.Sf, a δ v.1) *
      (∏ᶠ v : {v : FinPlace F // v ∉ S.Sf}, a δ v.1) at hsplit
    rw [finprod_eq_prod_of_fintype (fun v : S.Sf => a δ v.1)] at hsplit
    have hExt : (∏ᶠ v : {v : FinPlace F // v ∉ S.Sf}, a δ v.1) =
        whitExteriorTerm P G μ Fs x0 δ := by
      unfold whitExteriorTerm
      apply finprod_congr
      intro v
      dsimp only [a]
      rw [hext v.1 v.property, hx v.1 v.property]
    rw [hExt] at hsplit
    simpa only [whitTensorTerm, a, z, mul_comm] using hsplit
  rw [whit_atLift P G μ hs Fs' x]
  change (κF F)⁻¹ * (∑' δ, (∏ᶠ v, a δ v) * C) =
    ((κF F)⁻¹ * ∑' δ, whitTensorTerm P G μ Fs x0 z δ) * C
  simp_rw [hprod]
  rw [((whitTensorTerm_summable P G μ hs Fs x0 z).of_norm).tsum_mul_right C]
  simp only [mul_assoc]

/-- **eis:multilinear** (linearity at the places of `S_f`): with the exterior and complex data fixed,
`W_E(g)` is a multilinear form in the local Jacquet vectors at `S_f`. The convergence half-plane
is required per `sol-thin-thglobal` for the defining `tsum`. -/
theorem whittakerE_multilinear (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (Fs : GlobalSection P G s) (x0 : P.RP)
    (hs : (1 / 2 : ℝ) < s.re) :
    ∃ Λ : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ,
      ∀ (Fs' : GlobalSection P G s) (x : P.RP), (∀ v, v ∉ S.Sf → Fs'.f v = Fs.f v) →
        Fs'.fC = Fs.fC → (∀ v, v ∉ S.Sf → P.compF v x = P.compF v x0) →
        whittakerE P G μ Fs' (P.q x) =
          Λ (fun v => jacquet (P.loc v.1) A (μ v.1) (rtr (P.compF v.1 x) (Fs'.f v.1))) *
            ∏ w, jacquetC (rtr (P.compC w x) (Fs'.fC w)) := by
  obtain ⟨Λ, hΛ⟩ := whit_tensor_multilinear P G μ hs Fs x0
  refine ⟨Λ, ?_⟩
  intro Fs' x hext hC hx
  rw [hΛ]
  exact whit_tensor_formula P G μ hs Fs x0 Fs' x hext hC hx

end Eis

end ArtinPrimitiveRoots.A1.Theta
