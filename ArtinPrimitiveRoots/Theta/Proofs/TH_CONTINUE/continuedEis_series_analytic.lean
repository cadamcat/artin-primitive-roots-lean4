import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical BoundedContinuousFunction MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

private theorem continuedEis_contDomain_pos {ε : ℝ} (hε : ε ≤ 1 / 12) :
    ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε ⊆ {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re
  unfold ArtinPrimitiveRoots.A1.Spec.contDomain at hs
  simp only [Set.mem_union] at hs
  rcases hs with (hs | hs) | hs
  · exact hs.1
  · have hdist : ‖s - (5 / 2 : ℂ)‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hs
    have hRe : |s.re - (5 / 2 : ℝ)| < (1 / 2 : ℝ) := by
      calc
        |s.re - (5 / 2 : ℝ)| = |(s - (5 / 2 : ℂ)).re| := by simp
        _ ≤ ‖s - (5 / 2 : ℂ)‖ := Complex.abs_re_le_norm _
        _ < (1 / 2 : ℝ) := hdist
    have hlo := (abs_lt.mp hRe).1
    have hlow : (5 / 2 : ℝ) - 1 / 2 < s.re := by
      calc
        (5 / 2 : ℝ) - 1 / 2 = 5 / 2 + -(1 / 2 : ℝ) := by ring
        _ < 5 / 2 + (s.re - 5 / 2) := add_lt_add_right hlo (5 / 2 : ℝ)
        _ = s.re := by ring
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans
      ((by norm_num : (1 / 2 : ℝ) < (5 / 2 : ℝ) - 1 / 2).trans hlow)
  · have hdist : ‖s - (1 / 6 : ℂ)‖ < ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hs.1
    have hRe : |s.re - (1 / 6 : ℝ)| < ε := by
      calc
        |s.re - (1 / 6 : ℝ)| = |(s - (1 / 6 : ℂ)).re| := by simp
        _ ≤ ‖s - (1 / 6 : ℂ)‖ := Complex.abs_re_le_norm _
        _ < ε := hdist
    have hlo := (abs_lt.mp hRe).1
    have hsmall : ε < (1 / 6 : ℝ) := by
      calc
        ε ≤ 1 / 12 := hε
        _ < 1 / 6 := by norm_num
    have hbound : 0 < (1 / 6 : ℝ) - ε := sub_pos.mpr hsmall
    have hlow : (1 / 6 : ℝ) - ε < s.re := by
      calc
        (1 / 6 : ℝ) - ε = (1 / 6 : ℝ) + -ε := by ring
        _ < (1 / 6 : ℝ) + (s.re - 1 / 6) := add_lt_add_right hlo (1 / 6 : ℝ)
        _ = s.re := by ring
    exact hbound.trans hlow

private theorem continuedEis_residueBall_pos {ε : ℝ} (hε : ε ≤ 1 / 12) :
    Metric.ball (1 / 6 : ℂ) ε ⊆ {s : ℂ | 0 < s.re} := by
  intro s hs
  change 0 < s.re
  have hdist : ‖s - (1 / 6 : ℂ)‖ < ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  have hRe : |s.re - (1 / 6 : ℝ)| < ε := by
    calc
      |s.re - (1 / 6 : ℝ)| = |(s - (1 / 6 : ℂ)).re| := by simp
      _ ≤ ‖s - (1 / 6 : ℂ)‖ := Complex.abs_re_le_norm _
      _ < ε := hdist
  have hlo := (abs_lt.mp hRe).1
  have hsmall : ε < (1 / 6 : ℝ) := by
    calc
      ε ≤ 1 / 12 := hε
      _ < 1 / 6 := by norm_num
  have hbound : 0 < (1 / 6 : ℝ) - ε := sub_pos.mpr hsmall
  have hlow : (1 / 6 : ℝ) - ε < s.re := by
    calc
      (1 / 6 : ℝ) - ε = (1 / 6 : ℝ) + -ε := by ring
      _ < (1 / 6 : ℝ) + (s.re - 1 / 6) := add_lt_add_right hlo (1 / 6 : ℝ)
      _ = s.re := by ring
  exact hbound.trans hlow

private theorem continuedEis_spec_E_scalar_analytic {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] {Γ : Subgroup SL(2, 𝓞 F)} {σ : SL(2, F)}
    (d : ArtinPrimitiveRoots.A1.Spec.ContinuedEisenstein F Γ σ (1 / 6))
    (z : ArtinPrimitiveRoots.A1.Spec.X F) :
    ∃ φ : ℂ → ℂ,
      AnalyticOnNhd ℂ φ (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) d.ε) ∧
      ∀ s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) d.ε, φ s = d.E s z := by
  let p := ArtinPrimitiveRoots.A1.Spec.coordsX F z
  let K : Set (ArtinPrimitiveRoots.A1.Spec.Coord F) := {p}
  have hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro w
    change 0 < ArtinPrimitiveRoots.A1.Spec.height (z w)
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hK : IsCompact K := isCompact_singleton
  have hKpos : K ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    rintro q rfl
    exact hp
  obtain ⟨Φ, hΦ, hΦval⟩ := d.E_analytic K hK hKpos 0 (Fin.elim0)
  let pK : K := ⟨p, Set.mem_singleton p⟩
  let ev : (K →ᵇ ℂ) →L[ℂ] ℂ := BoundedContinuousFunction.evalCLM ℂ pK
  refine ⟨fun s => ev (Φ s), ev.comp_analyticOnNhd hΦ, ?_⟩
  intro s hs
  have hpt : ArtinPrimitiveRoots.A1.Spec.ptX F p = z := by
    funext w
    exact ArtinPrimitiveRoots.A1.Spec.pt_horiz_height (z w)
  have hval := hΦval s hs pK
  simpa [ev, BoundedContinuousFunction.evalCLM, p, pK, K, hpt,
    iteratedFDeriv_zero_apply, Function.comp_apply] using hval

private theorem continuedEis_spec_res_scalar_laurent {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] {Γ : Subgroup SL(2, 𝓞 F)} {σ : SL(2, F)}
    (d : ArtinPrimitiveRoots.A1.Spec.ContinuedEisenstein F Γ σ (1 / 6))
    (z : ArtinPrimitiveRoots.A1.Spec.X F) :
    ∃ ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ ψ (Metric.ball (1 / 6 : ℂ) d.ε) ∧
      ψ (1 / 6) = d.res z ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) d.ε, s ≠ 1 / 6 →
        ψ s = (s - 1 / 6) * d.E s z := by
  let p := ArtinPrimitiveRoots.A1.Spec.coordsX F z
  let K : Set (ArtinPrimitiveRoots.A1.Spec.Coord F) := {p}
  have hp : p ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro w
    change 0 < ArtinPrimitiveRoots.A1.Spec.height (z w)
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hK : IsCompact K := isCompact_singleton
  have hKpos : K ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    rintro q rfl
    exact hp
  obtain ⟨Ψ, hΨ, hΨcenter, hΨpunct⟩ := d.laurent K hK hKpos 0 (Fin.elim0)
  let pK : K := ⟨p, Set.mem_singleton p⟩
  let ev : (K →ᵇ ℂ) →L[ℂ] ℂ := BoundedContinuousFunction.evalCLM ℂ pK
  have hpt : ArtinPrimitiveRoots.A1.Spec.ptX F p = z := by
    funext w
    exact ArtinPrimitiveRoots.A1.Spec.pt_horiz_height (z w)
  have hcast : ((1 / 6 : ℝ) : ℂ) = (1 / 6 : ℂ) := by norm_num
  have hΨ' : AnalyticOnNhd ℂ (fun s => ev (Ψ s))
      (Metric.ball (1 / 6 : ℂ) d.ε) := by
    have hcomp := ev.comp_analyticOnNhd hΨ
    have hcomp' : AnalyticOnNhd ℂ (fun s => ev (Ψ s))
        (Metric.ball ((1 / 6 : ℝ) : ℂ) d.ε) := by
      exact hcomp.congr Metric.isOpen_ball (by intro s hs; rfl)
    simpa [hcast] using hcomp'
  refine ⟨fun s => ev (Ψ s), hΨ', ?_, ?_⟩
  · have hval := hΨcenter pK
    simpa [ev, BoundedContinuousFunction.evalCLM, p, pK, K, hpt,
      iteratedFDeriv_zero_apply, Function.comp_apply] using hval
  · intro s hs hne
    have hs' : s ∈ Metric.ball ((1 / 6 : ℝ) : ℂ) d.ε := by simpa [hcast] using hs
    have hne' : s ≠ ((1 / 6 : ℝ) : ℂ) := by simpa [hcast] using hne
    have hval := hΨpunct s hs' hne' pK
    simpa [ev, BoundedContinuousFunction.evalCLM, p, pK, K, hpt,
      iteratedFDeriv_zero_apply, Function.comp_apply] using hval

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The reconstructed sums agree with the adelic series on the baseline ball, are analytic
on the continuation domain, and have the prescribed scalar Laurent fields at every point.
Uses component/reconstruction data, `Spec.ContinuedEisenstein.E_series`, its Banach-valued
`E_analytic` and `laurent` at derivative order zero. Consumed by `exists_continuedEis`. -/
theorem continuedEis_series_analytic {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) :
    (∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ g,
      R.E s g = eisenstein P G (I.sec s) g) ∧
    (∀ g, AnalyticOnNhd ℂ (fun s => R.E s g)
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε)) ∧
    ∀ g, ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) C.ε) ∧
      Ψ (1 / 6) = R.theta g ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) C.ε,
        s ≠ 1 / 6 → Ψ s = (s - 1 / 6) * R.E s g := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs g
    obtain ⟨j, a, z, hE, hθ, horig⟩ := R.point_transport g
    have hdom : s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε := by
      change s ∈ _ ∪ _ ∪ _
      exact Or.inl (Or.inr hs)
    have hsRe : (1 / 2 : ℝ) < s.re := by
      have hdist : ‖s - (5 / 2 : ℂ)‖ < (1 / 2 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hs
      have hRe : |s.re - (5 / 2 : ℝ)| < (1 / 2 : ℝ) := by
        calc
          |s.re - (5 / 2 : ℝ)| = |(s - (5 / 2 : ℂ)).re| := by simp
          _ ≤ ‖s - (5 / 2 : ℂ)‖ := Complex.abs_re_le_norm _
          _ < (1 / 2 : ℝ) := hdist
      have hlo := (abs_lt.mp hRe).1
      have hlow : (5 / 2 : ℝ) - 1 / 2 < s.re := by
        calc
          (5 / 2 : ℝ) - 1 / 2 = 5 / 2 + -(1 / 2 : ℝ) := by ring
          _ < 5 / 2 + (s.re - 5 / 2) := add_lt_add_right hlo (5 / 2 : ℝ)
          _ = s.re := by ring
      exact (by norm_num : (1 / 2 : ℝ) < (5 / 2 : ℝ) - 1 / 2).trans hlow
    calc
      R.E s g = a * C.componentE j s z := hE s hdom
      _ = a * (∑ i, C.c j i s * (C.d j i).E s z) := rfl
      _ = a * (∑ i, C.c j i s *
          ArtinPrimitiveRoots.A1.Spec.eisSeries F (C.Γ j) (C.σ j i) s z) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        congr 2
        exact (C.d j i).E_series s hs z
      _ = a * ArtinPrimitiveRoots.A1.Theta.classicalOf P
          (fun h => ArtinPrimitiveRoots.A1.Theta.eisenstein P G (I.sec s) h) j z := by
        rw [C.series_component j s hsRe z]
      _ = ArtinPrimitiveRoots.A1.Theta.eisenstein P G (I.sec s) g := (horig s hs).symm
  · intro g
    obtain ⟨j, a, z, hE, hθ, horig⟩ := R.point_transport g
    have hpos := continuedEis_contDomain_pos C.ε_le
    let hsum : ∀ i : Fin (C.cuspCount j),
        AnalyticOnNhd ℂ (fun s => C.c j i s * (C.d j i).E s z)
          (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε) := by
      intro i
      obtain ⟨φ, hφ, hφval⟩ := continuedEis_spec_E_scalar_analytic (C.d j i) z
      have hc : AnalyticOnNhd ℂ (C.c j i)
          (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε) := by
        exact (C.c_analytic j i).mono hpos
      have hφ' : AnalyticOnNhd ℂ φ
          (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε) := by
        simpa [C.d_radius j i] using hφ
      have hmul := hc.mul hφ'
      have hmulEq : (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε).EqOn
          (fun s => C.c j i s * φ s) (fun s => C.c j i s * (C.d j i).E s z) := by
        intro s hs
        have hs' : s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) (C.d j i).ε := by
          simpa [C.d_radius j i] using hs
        change C.c j i s * φ s = C.c j i s * (C.d j i).E s z
        rw [hφval s hs']
      exact hmul.congr (ArtinPrimitiveRoots.A1.Spec.isOpen_contDomain (1 / 6) C.ε) hmulEq
    have hsumAnalytic := Finset.analyticOnNhd_fun_sum
      (Finset.univ : Finset (Fin (C.cuspCount j))) (fun i hi => hsum i)
    have ha : AnalyticOnNhd ℂ (fun _ : ℂ => a)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε) := analyticOnNhd_const
    have hprod := ha.mul hsumAnalytic
    have hEq : (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε).EqOn
        (fun s => a * ∑ i, C.c j i s * (C.d j i).E s z) (fun s => R.E s g) := by
      intro s hs
      change a * (∑ i, C.c j i s * (C.d j i).E s z) = R.E s g
      exact (hE s hs).symm
    exact hprod.congr (ArtinPrimitiveRoots.A1.Spec.isOpen_contDomain (1 / 6) C.ε) hEq
  · intro g
    obtain ⟨j, a, z, hE, hθ, horig⟩ := R.point_transport g
    -- The finite cusp sum uses the same scalar Laurent field at each cusp.
    classical
    let ψ : ℂ → ℂ := fun s => a * ∑ i, C.c j i s * Classical.choose
      (continuedEis_spec_res_scalar_laurent (C.d j i) z) s
    have hψAnalytic : AnalyticOnNhd ℂ ψ (Metric.ball (1 / 6 : ℂ) C.ε) := by
      dsimp [ψ]
      have hsum : AnalyticOnNhd ℂ
          (fun s => ∑ i, C.c j i s * Classical.choose
            (continuedEis_spec_res_scalar_laurent (C.d j i) z) s)
          (Metric.ball (1 / 6 : ℂ) C.ε) := by
        apply Finset.analyticOnNhd_fun_sum (Finset.univ : Finset (Fin (C.cuspCount j)))
        intro i hi
        let φ := Classical.choose
          (continuedEis_spec_res_scalar_laurent (C.d j i) z)
        have hφspec := Classical.choose_spec
          (continuedEis_spec_res_scalar_laurent (C.d j i) z)
        obtain ⟨hφ, _, _⟩ := hφspec
        have hc : AnalyticOnNhd ℂ (C.c j i) (Metric.ball (1 / 6 : ℂ) C.ε) := by
          exact (C.c_analytic j i).mono (continuedEis_residueBall_pos C.ε_le)
        have hφ' : AnalyticOnNhd ℂ φ (Metric.ball (1 / 6 : ℂ) C.ε) := by
          have hrad : C.ε ≤ (C.d j i).ε := by rw [← C.d_radius j i]
          exact hφ.mono (Metric.ball_subset_ball hrad)
        exact hc.mul hφ'
      exact (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => a) _).mul hsum
    refine ⟨ψ, hψAnalytic, ?_, ?_⟩
    · rw [hθ]
      dsimp [ψ, ContinuedEisComponents.componentTheta]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hφspec := Classical.choose_spec
        (continuedEis_spec_res_scalar_laurent (C.d j i) z)
      obtain ⟨_, hφ0, _⟩ := hφspec
      exact congrArg (fun q => C.c j i (1 / 6) * q) hφ0
    · intro s hs hne
      dsimp [ψ]
      rw [hE s (by
        change s ∈ _ ∪ _ ∪ _
        have hcast : ((1 / 6 : ℝ) : ℂ) = (1 / 6 : ℂ) := by norm_num
        have hs' : s ∈ Metric.ball ((1 / 6 : ℝ) : ℂ) C.ε := by
          simpa [hcast] using hs
        have hne' : s ≠ ((1 / 6 : ℝ) : ℂ) := by
          simpa [hcast] using hne
        exact Or.inr ⟨hs', by simpa [Set.mem_singleton_iff] using hne'⟩)]
      simp only [ContinuedEisComponents.componentE]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hφspec := Classical.choose_spec
        (continuedEis_spec_res_scalar_laurent (C.d j i) z)
      obtain ⟨_, _, hφp⟩ := hφspec
      have hsdi : s ∈ Metric.ball (1 / 6 : ℂ) (C.d j i).ε := by
        exact Metric.ball_subset_ball (by rw [← C.d_radius j i]) hs
      have hne' : s ≠ 1 / 6 := hne
      rw [hφp s hsdi hne']
      ring

end ArtinPrimitiveRoots.A1.Theta
