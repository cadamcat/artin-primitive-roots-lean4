import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Spec.Interface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.LocalWhit

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

/-- **eis:global-datum** (existence). The strengthened datum is required by C6 of
`sol-gate-theta`. -/
theorem exists_globalDatum (P : CoverPackage D S H A) (hSt : ∀ v, SteinbergAt H v) :
    Nonempty (GlobalDatum P) := by
  sorry

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

/-- **eis:converge** (via P-REDUCTION and P-SPEC `eisSeries_majorant`): absolute convergence for
`Re s > 1/2`. C6 of `sol-gate-theta` strengthens the input datum to exclude divergent cube repeats. -/
theorem eisenstein_summable (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) (g : P.tc.G) :
    Summable fun γ : Quotient (QuotientGroup.rightRel (Bstar G)) =>
      ‖scalarOf P G Fs.f Fs.fC (P.tc.rat (Quotient.out γ) * g)‖ := by
  sorry

/-- **eis:automorphic**: in the convergence region `E` is automorphic, genuine, and right-invariant
under every element fixing all local sections. -/
theorem eisenstein_automorphic (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (hs : 1 / 2 < s.re) (Fs : GlobalSection P G s) :
    (∀ γ g, eisenstein P G Fs (P.tc.rat γ * g) = eisenstein P G Fs g) ∧
    (∀ ζ g, eisenstein P G Fs (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * eisenstein P G Fs g) ∧
    (∀ k : P.tc.G, (∀ h, scalarOf P G Fs.f Fs.fC (h * k) = scalarOf P G Fs.f Fs.fC h) →
      ∀ g, eisenstein P G Fs (g * k) = eisenstein P G Fs g) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Eis

end ArtinPrimitiveRoots.A1.Theta
