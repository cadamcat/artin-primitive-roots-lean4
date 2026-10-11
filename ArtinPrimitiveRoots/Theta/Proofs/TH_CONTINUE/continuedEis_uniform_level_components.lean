import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private structure ContinuedEisLocalDecomp {P : CoverPackage D S H A} {G : GlobalDatum P}
    (I : ContinuedEisInput P G) (j : P.tc.G) where
  Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))
  finiteIndex : Γ.FiniteIndex
  free : ArtinPrimitiveRoots.A1.Spec.FreeAction F Γ
  cuspCount : ℕ
  σ : Fin cuspCount → Matrix.SpecialLinearGroup (Fin 2) F
  c : Fin cuspCount → ℂ → ℂ
  c_analytic : ∀ i, AnalyticOnNhd ℂ (fun s => c i s) {s | 0 < s.re}
  series : ∀ s : ℂ, 1 / 2 < s.re → ∀ (x : InfinitePlace F → ℂ)
    (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
    eisenstein P G (I.sec s) (nInf P x * aInf P y * j) =
      ∑ i, c i s * ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ (σ i) s
        (ArtinPrimitiveRoots.A1.Spec.ptX' F x y)

/-- Choose the uniform finite level and common finite components, decompose each component
into cusps, and restrict all spectral continuations to the same radius at most `1/12`.
Uses frozen `scalarOf_q`, `exists_classical_components`, `red_decompose`,
`Spec.exists_continuedEisenstein` and proved `Spec.ContinuedEisenstein.exists_restrict`.
Consumed by component reconstruction and frozen `exists_continuedEis`. -/
theorem continuedEis_uniform_level_components {P : CoverPackage D S H A} {G : GlobalDatum P}
    (I : ContinuedEisInput P G) : Nonempty (ContinuedEisComponents I) := by
  classical
  let T0 := I.T0
  have hsub : S.Sf ⊆ T0 := by
    intro v hv
    have h := (I.sec 0).sub hv
    rw [I.T0_eq 0] at h
    exact h
  let m : FinPlace F → ℕ := fun v =>
    if hv : v ∈ T0 then Classical.choose (I.level v hv) else (P.loc v).m0
  have hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v := by
    intro v hv
    simp only [m, dif_pos hv]
    exact (Classical.choose_spec (I.level v hv)).1
  have hlocal_level (v : FinPlace F) (hv : v ∈ T0) (s : ℂ) (g k : (P.loc v).L)
      (hk : k ∈ (P.loc v).Kc (m v)) :
      (I.sec s).f v (g * k) = (I.sec s).f v g := by
    have h := (Classical.choose_spec (I.level v hv)).2 s g k
    apply h
    simpa [m, hv] using hk
  have hlevel : ∀ s g, ∀ k ∈ levelSet P T0 hsub m,
      scalarOf P G (I.sec s).f (I.sec s).fC (g * k) =
        scalarOf P G (I.sec s).f (I.sec s).fC g := by
    intro s g k hk
    rcases hk with ⟨xk, hqk, hc, hf, ho⟩
    obtain ⟨xg, hqg⟩ := P.q_surj g
    have hlocal : ∀ v,
        G.lam v ((I.sec s).f v (P.compF v xg * P.compF v xk)) =
          G.lam v ((I.sec s).f v (P.compF v xg)) := by
      intro v
      by_cases hv : v ∈ T0
      · exact congrArg (G.lam v)
          (hlocal_level v hv s (P.compF v xg) (P.compF v xk) (hf v hv))
      · apply congrArg (G.lam v)
        have hv' : v ∉ (I.sec s).T0 := by rw [I.T0_eq s]; exact hv
        exact ((I.sec s).f_sph v hv').2 (P.compF v xg) (P.compF v xk) (ho v hv)
    have hfinprod :
        (∏ᶠ v, G.lam v ((I.sec s).f v (P.compF v xg * P.compF v xk))) =
          ∏ᶠ v, G.lam v ((I.sec s).f v (P.compF v xg)) := by
      apply finprod_congr
      intro v
      exact hlocal v
    have hfinprod_map :
        (∏ᶠ v, G.lam v ((I.sec s).f v (P.compF v (xg * xk)))) =
          ∏ᶠ v, G.lam v ((I.sec s).f v (P.compF v xg * P.compF v xk)) := by
      apply finprod_congr
      intro v
      rw [(P.compF v).map_mul]
    have harch_map :
        (∏ w, (I.sec s).fC w (P.compC w (xg * xk))) =
          ∏ w, (I.sec s).fC w (P.compC w xg * P.compC w xk) := by
      apply Finset.prod_congr rfl
      intro w hw
      rw [(P.compC w).map_mul]
    have harch :
        (∏ w, (I.sec s).fC w (P.compC w xg * P.compC w xk)) =
          ∏ w, (I.sec s).fC w (P.compC w xg) := by
      apply Finset.prod_congr rfl
      intro w hw
      rw [hc w, mul_one]
    calc
      scalarOf P G (I.sec s).f (I.sec s).fC (g * k) =
          scalarOf P G (I.sec s).f (I.sec s).fC (P.q (xg * xk)) := by
            rw [(P.q).map_mul, hqg, hqk]
      _ = (∏ᶠ v, G.lam v ((I.sec s).f v (P.compF v (xg * xk)))) *
            ∏ w, (I.sec s).fC w (P.compC w (xg * xk)) :=
          (scalarOf_q P G (I.sec s) (xg * xk)).2
      _ = (∏ᶠ v, G.lam v ((I.sec s).f v (P.compF v xg))) *
            ∏ w, (I.sec s).fC w (P.compC w xg) := by
          rw [hfinprod_map, harch_map, hfinprod, harch]
      _ = scalarOf P G (I.sec s).f (I.sec s).fC (P.q xg) :=
          ((scalarOf_q P G (I.sec s) xg).2).symm
      _ = scalarOf P G (I.sec s).f (I.sec s).fC g := by rw [hqg]
  obtain ⟨J, hJ, hdetect⟩ := exists_classical_components P T0 hsub m hm
  have hdata : ∀ (j : {j : P.tc.G // j ∈ J}), Nonempty (ContinuedEisLocalDecomp I j.1) := by
    intro j
    rcases red_decompose P G I.sec T0 I.T0_eq hsub I.fC_sph m hm hlevel I.f_analytic
        j.1 (hJ j.1 j.2) with
      ⟨Γ, hΓ, hfree, ι, hι, σ, c, hc, hseries⟩
    letI : Fintype ι := hι
    let n := Fintype.card ι
    let e : ι ≃ Fin n := Fintype.equivFin ι
    refine ⟨{
      Γ := Γ
      finiteIndex := hΓ
      free := hfree
      cuspCount := n
      σ := σ ∘ e.symm
      c := c ∘ e.symm
      c_analytic := ?_
      series := ?_
    }⟩
    · intro i
      exact hc (e.symm i)
    · intro s hs x y hy
      let f : Fin n → ℂ := fun i =>
        c (e.symm i) s *
          ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ (σ (e.symm i)) s
            (ArtinPrimitiveRoots.A1.Spec.ptX' F x y)
      have hsum :
          (∑ i : ι, c i s * ArtinPrimitiveRoots.A1.Spec.eisSeries F Γ (σ i) s
            (ArtinPrimitiveRoots.A1.Spec.ptX' F x y)) = ∑ i : Fin n, f i := by
        simpa [f] using Equiv.sum_comp e f
      simpa [Function.comp_apply, f] using (hseries s hs x y hy).2.trans hsum
  let dec : ∀ (j : {j : P.tc.G // j ∈ J}), ContinuedEisLocalDecomp I j.1 :=
    fun j => Classical.choice (hdata j)
  let Γfun : (j : {j : P.tc.G // j ∈ J}) →
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)) := fun j => (dec j).Γ
  let nfun : (j : {j : P.tc.G // j ∈ J}) → ℕ := fun j => (dec j).cuspCount
  let σfun : (j : {j : P.tc.G // j ∈ J}) → Fin (nfun j) →
      Matrix.SpecialLinearGroup (Fin 2) F := fun j => (dec j).σ
  let cfun : (j : {j : P.tc.G // j ∈ J}) → Fin (nfun j) → ℂ → ℂ :=
    fun j => (dec j).c
  have hΓfinite : ∀ j : {j : P.tc.G // j ∈ J}, (Γfun j).FiniteIndex :=
    fun j => (dec j).finiteIndex
  have hΓfree : ∀ j : {j : P.tc.G // j ∈ J},
      ArtinPrimitiveRoots.A1.Spec.FreeAction F (Γfun j) := fun j => (dec j).free
  have hc_analytic : ∀ (j : {j : P.tc.G // j ∈ J}) (i : Fin (nfun j)),
      AnalyticOnNhd ℂ (cfun j i) {s | 0 < s.re} :=
    fun j => (dec j).c_analytic
  have hseries_component : ∀ j : {j : P.tc.G // j ∈ J},
      ∀ s : ℂ, 1 / 2 < s.re → ∀ (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ),
        (∀ w, 0 < y w) →
        eisenstein P G (I.sec s) (nInf P x * aInf P y * j.1) =
          ∑ i, cfun j i s * ArtinPrimitiveRoots.A1.Spec.eisSeries F (Γfun j)
            (σfun j i) s (ArtinPrimitiveRoots.A1.Spec.ptX' F x y) :=
    fun j => (dec j).series
  let d₀ : ∀ (j : {j : P.tc.G // j ∈ J}) (i : Fin (nfun j)),
      ArtinPrimitiveRoots.A1.Spec.ContinuedEisenstein F (Γfun j) (σfun j i) (1 / 6 : ℝ) :=
    fun j i => by
      letI : (Γfun j).FiniteIndex := hΓfinite j
      exact Classical.choice
        (ArtinPrimitiveRoots.A1.Spec.exists_continuedEisenstein F (Γfun j) (hΓfree j)
          (σfun j i) (1 / 6 : ℝ) (by norm_num) (by norm_num))
  let Idx := Σ j : {j : P.tc.G // j ∈ J}, Fin (nfun j)
  let epsFn : Option Idx → ℝ := fun q =>
    match q with
    | none => (1 / 12 : ℝ)
    | some ij => (d₀ ij.1 ij.2).ε
  have hidx : (Finset.univ : Finset (Option Idx)).Nonempty :=
    ⟨none, Finset.mem_univ _⟩
  let ε : ℝ := Finset.univ.inf' hidx epsFn
  have hepsFn_pos : ∀ q, 0 < epsFn q := by
    intro q
    cases q with
    | none => norm_num [epsFn]
    | some ij => exact (d₀ ij.1 ij.2).ε_pos
  have hεpos : 0 < ε := by
    dsimp [ε]
    rw [Finset.lt_inf'_iff]
    intro q hq
    exact hepsFn_pos q
  have hεle (j : {j : P.tc.G // j ∈ J}) (i : Fin (nfun j)) :
      ε ≤ (d₀ j i).ε := by
    change Finset.univ.inf' hidx epsFn ≤ epsFn (some (⟨j, i⟩ : Idx))
    exact Finset.inf'_le epsFn (Finset.mem_univ (some (⟨j, i⟩ : Idx)))
  have hεle12 : ε ≤ (1 / 12 : ℝ) := by
    change Finset.univ.inf' hidx epsFn ≤ epsFn none
    exact Finset.inf'_le epsFn (Finset.mem_univ (none : Option Idx))
  let restrictSpec (j : {j : P.tc.G // j ∈ J}) (i : Fin (nfun j)) :=
    ArtinPrimitiveRoots.A1.Spec.ContinuedEisenstein.exists_restrict (F := F)
      (d₀ j i) ε hεpos (hεle j i)
  let d : ∀ (j : {j : P.tc.G // j ∈ J}) (i : Fin (nfun j)),
      ArtinPrimitiveRoots.A1.Spec.ContinuedEisenstein F (Γfun j) (σfun j i) (1 / 6 : ℝ) :=
    fun j i => Classical.choose (restrictSpec j i)
  have hd_radius : ∀ (j : {j : P.tc.G // j ∈ J}) (i : Fin (nfun j)), (d j i).ε = ε :=
    fun j i => (Classical.choose_spec (restrictSpec j i)).1
  refine ⟨{
    hsub := hsub
    m := m
    hm := hm
    hlevel := hlevel
    J := J
    finite_components := hJ
    detect := hdetect
    ε := ε
    ε_pos := hεpos
    ε_le := hεle12
    Γ := Γfun
    finiteIndex := hΓfinite
    free := hΓfree
    cuspCount := nfun
    σ := σfun
    c := cfun
    c_analytic := hc_analytic
    d := d
    d_radius := hd_radius
    series_component := ?_
  }⟩
  intro j s hs z
  let x : InfinitePlace F → ℂ := fun w => ArtinPrimitiveRoots.A1.Spec.horiz (z w)
  let y : InfinitePlace F → ℝ := fun w => ArtinPrimitiveRoots.A1.Spec.height (z w)
  have hy : ∀ w, 0 < y w := by
    intro w
    change 0 < ArtinPrimitiveRoots.A1.Spec.height (z w)
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hpt : ArtinPrimitiveRoots.A1.Spec.ptX' F x y = z := by
    funext w
    exact ArtinPrimitiveRoots.A1.Spec.pt_horiz_height (z w)
  have hsum := hseries_component j s hs x y hy
  simpa [classicalOf, x, y, hpt] using hsum

end ArtinPrimitiveRoots.A1.Theta
