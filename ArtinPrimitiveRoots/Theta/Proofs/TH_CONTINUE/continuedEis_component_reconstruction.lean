import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_unique
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_representatives

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private def sphericalCDen (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2

private theorem sphericalCDen_eq (g : Matrix (Fin 2) (Fin 2) ℂ) :
    sphericalCDen g = ((g * star g) 1 1).re := by
  rw [sphericalCDen, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq]

private theorem det_star (g : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.det (star g) = star (Matrix.det g) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]

private theorem det_norm_unitary (k : GL (Fin 2) ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
  have hk' : (k : Matrix (Fin 2) (Fin 2) ℂ) * star (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hk
  have hdet : Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ) *
      star (Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    calc
      _ = Matrix.det ((k : Matrix (Fin 2) (Fin 2) ℂ) * star (k : Matrix (Fin 2) (Fin 2) ℂ)) := by
        rw [Matrix.det_mul, det_star]
      _ = 1 := by rw [hk']; simp
  have hnorm : ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 = 1 := by
    have h := congrArg (fun z : ℂ => ‖z‖) hdet
    simpa only [norm_mul, norm_star, norm_one, sq] using h
  have hnonneg : 0 ≤ ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ := norm_nonneg _
  nlinarith

private theorem sphericalC_right_unitary (s : ℂ) (g k : GL (Fin 2) ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ArtinPrimitiveRoots.A1.Theta.sphericalC s (g * k) =
      ArtinPrimitiveRoots.A1.Theta.sphericalC s g := by
  have hk' : (k : Matrix (Fin 2) (Fin 2) ℂ) * star (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hk
  have hden : sphericalCDen
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ)) =
      sphericalCDen (g : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [sphericalCDen_eq, sphericalCDen_eq]
    change ((((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ)) *
      star ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ))) 1 1).re = _
    rw [Matrix.star_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (k : Matrix (Fin 2) (Fin 2) ℂ)
        (star (k : Matrix (Fin 2) (Fin 2) ℂ)) (star (g : Matrix (Fin 2) (Fin 2) ℂ)), hk']
    simp
  have hratio :
      (‖Matrix.det ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ))‖ /
        sphericalCDen ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ))) =
      (‖Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ)‖ /
        sphericalCDen (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [Matrix.det_mul, Complex.norm_mul, det_norm_unitary k hk, mul_one, hden]
  simpa [ArtinPrimitiveRoots.A1.Theta.sphericalC, sphericalCDen] using
    congrArg (fun x : ℝ => (x : ℂ) ^ (1 + 2 * s)) hratio

private theorem continuedEis_scalar_right_infCompact
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    (I : ContinuedEisInput P G) (s : ℂ) (u : P.tc.G) (hu : u ∈ infCompact P)
    (h : P.tc.G) :
    scalarOf P G (I.sec s).f (I.sec s).fC (h * u) =
      scalarOf P G (I.sec s).f (I.sec s).fC h := by
  classical
  rcases hu with ⟨xu, hqu, hfu, hcu⟩
  obtain ⟨xh, hqh⟩ := P.q_surj h
  have hfin : (∏ᶠ v, G.lam v ((I.sec s).f v (P.compF v (xh * xu)))) =
      ∏ᶠ v, G.lam v ((I.sec s).f v (P.compF v xh)) := by
    apply finprod_congr
    intro v
    rw [(P.compF v).map_mul, hfu v, mul_one]
  have harch : (∏ w, (I.sec s).fC w (P.compC w (xh * xu))) =
      ∏ w, (I.sec s).fC w (P.compC w xh) := by
    apply Finset.prod_congr rfl
    intro w hw
    rw [(P.compC w).map_mul, I.fC_sph]
    rcases hcu w with ⟨kw, hkw, hcomp⟩
    rw [hcomp]
    let gw : GL (Fin 2) ℂ := Quotient.out (P.compC w xh)
    have hgw : QuotientGroup.mk gw = P.compC w xh := Quotient.out_eq _
    have hqmul : P.compC w xh * QuotientGroup.mk kw = QuotientGroup.mk (gw * kw) := by
      rw [← hgw]
      simp
    rw [hqmul, ArtinPrimitiveRoots.A1.Theta.sphC_mk,
      sphericalC_right_unitary s gw kw hkw, ← hgw,
      ArtinPrimitiveRoots.A1.Theta.sphC_mk]
  calc
    scalarOf P G (I.sec s).f (I.sec s).fC (h * u) =
        scalarOf P G (I.sec s).f (I.sec s).fC (P.q (xh * xu)) := by
          rw [(P.q).map_mul, hqh, hqu]
    _ = (∏ᶠ v, G.lam v ((I.sec s).f v (P.compF v (xh * xu)))) *
          ∏ w, (I.sec s).fC w (P.compC w (xh * xu)) :=
        (scalarOf_q P G (I.sec s) (xh * xu)).2
    _ = (∏ᶠ v, G.lam v ((I.sec s).f v (P.compF v xh))) *
          ∏ w, (I.sec s).fC w (P.compC w xh) := by rw [hfin, harch]
    _ = scalarOf P G (I.sec s).f (I.sec s).fC (P.q xh) :=
        ((scalarOf_q P G (I.sec s) xh).2).symm
    _ = scalarOf P G (I.sec s).f (I.sec s).fC h := by rw [hqh]

private theorem continuedEis_contDomain_pos (ε : ℝ) (hε : ε ≤ (1 / 12 : ℝ)) :
    ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε ⊆ {s : ℂ | 0 < s.re} := by
  intro s hs
  simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hs
  rcases hs with (hs | hs) | hs
  · exact hs.1
  · have hb := Metric.mem_ball.mp hs
    have habs : |s.re - (5 / 2 : ℝ)| < (1 / 2 : ℝ) := by
      have hle := Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
      rw [dist_eq_norm] at hb
      simpa [Complex.sub_re] using lt_of_le_of_lt hle hb
    have hlow := (abs_lt.mp habs).1
    change 0 < s.re
    nlinarith [hlow]
  · have hb := Metric.mem_ball.mp hs.1
    have habs : |s.re - (1 / 6 : ℝ)| < (1 / 12 : ℝ) := by
      have hle := Complex.abs_re_le_norm (s - (1 / 6 : ℂ))
      rw [dist_eq_norm] at hb
      exact lt_of_le_of_lt (by simpa [Complex.sub_re] using hle)
        (lt_of_lt_of_le hb hε)
    have hlow := (abs_lt.mp habs).1
    change 0 < s.re
    nlinarith [hlow]

private theorem continuedEis_ball_pos (ε : ℝ) (hε : ε ≤ (1 / 12 : ℝ)) :
    Metric.ball (1 / 6 : ℂ) ε ⊆ {s : ℂ | 0 < s.re} := by
  intro s hs
  have hb := Metric.mem_ball.mp hs
  have habs : |s.re - (1 / 6 : ℝ)| < (1 / 12 : ℝ) := by
    have hle := Complex.abs_re_le_norm (s - (1 / 6 : ℂ))
    rw [dist_eq_norm] at hb
    exact lt_of_le_of_lt (by simpa [Complex.sub_re] using hle) (lt_of_lt_of_le hb hε)
  have hlow := (abs_lt.mp habs).1
  change 0 < s.re
  nlinarith [hlow]

private theorem continuedEis_point_data
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))}
    {σ : Matrix.SpecialLinearGroup (Fin 2) F}
    (d : ArtinPrimitiveRoots.A1.Spec.ContinuedEisenstein F Γ σ (1 / 6 : ℝ))
    (z : ArtinPrimitiveRoots.A1.Spec.X F) :
    AnalyticOnNhd ℂ (fun s => d.E s z)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) d.ε) ∧
      ∃ Ψ : ℂ → ℂ,
        AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) d.ε) ∧
        Ψ (1 / 6) = d.res z ∧
        ∀ s ∈ Metric.ball (1 / 6 : ℂ) d.ε, s ≠ 1 / 6 →
          Ψ s = (s - 1 / 6) * d.E s z := by
  classical
  let K : Set (ArtinPrimitiveRoots.A1.Spec.Coord F) :=
    {ArtinPrimitiveRoots.A1.Spec.coordsX F z}
  have hK : IsCompact K := isCompact_singleton
  have hpos : ArtinPrimitiveRoots.A1.Spec.coordsX F z ∈
      ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro w
    change 0 < ArtinPrimitiveRoots.A1.Spec.height (z w)
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hKP : K ⊆ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro p hp
    have : p = ArtinPrimitiveRoots.A1.Spec.coordsX F z := by simpa [K] using hp
    rw [this]
    exact hpos
  let p : K := ⟨ArtinPrimitiveRoots.A1.Spec.coordsX F z, by simp [K]⟩
  have hpt : ArtinPrimitiveRoots.A1.Spec.ptX F (ArtinPrimitiveRoots.A1.Spec.coordsX F z) = z := by
    funext w
    exact ArtinPrimitiveRoots.A1.Spec.pt_horiz_height (z w)
  obtain ⟨Φ, hΦ, hΦvalue⟩ := d.E_analytic K hK hKP 0 Fin.elim0
  have hEval : AnalyticOnNhd ℂ (fun s => BoundedContinuousFunction.evalCLM ℂ p (Φ s))
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) d.ε) := by
    change AnalyticOnNhd ℂ ((BoundedContinuousFunction.evalCLM ℂ p) ∘ Φ)
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) d.ε)
    exact (BoundedContinuousFunction.evalCLM ℂ p).comp_analyticOnNhd hΦ
  have hEq : (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) d.ε).EqOn
      (fun s => BoundedContinuousFunction.evalCLM ℂ p (Φ s)) (fun s => d.E s z) := by
    intro s hs
    have h := hΦvalue s hs p
    simpa [p, hpt] using h
  have hEanalytic := hEval.congr
    (ArtinPrimitiveRoots.A1.Spec.isOpen_contDomain (1 / 6) d.ε) hEq
  obtain ⟨Ψ, hΨ, hcenter, hpunct⟩ := d.laurent K hK hKP 0 Fin.elim0
  let ψ : ℂ → ℂ := fun s => BoundedContinuousFunction.evalCLM ℂ p (Ψ s)
  have hψanalytic : AnalyticOnNhd ℂ ψ (Metric.ball (1 / 6 : ℂ) d.ε) := by
    convert (BoundedContinuousFunction.evalCLM ℂ p).comp_analyticOnNhd hΨ using 1 <;>
      norm_num <;> rfl
  have hψcenter : ψ (1 / 6) = d.res z := by
    have h := hcenter p
    simpa [ψ, p, hpt] using h
  refine ⟨hEanalytic, ⟨ψ, hψanalytic, hψcenter, ?_⟩⟩
  intro s hs hne
  have hne' : s ≠ ((1 / 6 : ℝ) : ℂ) := by simpa using hne
  have h := hpunct s (by simpa using hs) hne' p
  simpa [ψ, p, hpt] using h

private theorem continuedEis_component_data
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I)
    (j : C.J) (z : ArtinPrimitiveRoots.A1.Spec.X F) :
    AnalyticOnNhd ℂ (fun s => C.componentE j s z)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε) ∧
      ∃ Ψ : ℂ → ℂ,
        AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) C.ε) ∧
        Ψ (1 / 6) = C.componentTheta j z ∧
        ∀ s ∈ Metric.ball (1 / 6 : ℂ) C.ε, s ≠ 1 / 6 →
          Ψ s = (s - 1 / 6) * C.componentE j s z := by
  classical
  have hEpoint (i : Fin (C.cuspCount j)) :
      AnalyticOnNhd ℂ (fun s => (C.d j i).E s z)
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε) := by
    simpa [C.d_radius j i] using (continuedEis_point_data (C.d j i) z).1
  have hpsiExist (i : Fin (C.cuspCount j)) :
      ∃ ψ : ℂ → ℂ,
        AnalyticOnNhd ℂ ψ (Metric.ball (1 / 6 : ℂ) C.ε) ∧
        ψ (1 / 6) = (C.d j i).res z ∧
        ∀ s ∈ Metric.ball (1 / 6 : ℂ) C.ε, s ≠ 1 / 6 →
          ψ s = (s - 1 / 6) * (C.d j i).E s z := by
    rcases (continuedEis_point_data (C.d j i) z).2 with ⟨ψ, hψ, hcenter, hpunct⟩
    refine ⟨ψ, ?_, hcenter, ?_⟩
    · simpa [C.d_radius j i] using hψ
    · intro s hs hne
      apply hpunct s ?_ hne
      simpa [C.d_radius j i] using hs
  let ψ : ∀ i : Fin (C.cuspCount j), ℂ → ℂ := fun i => Classical.choose (hpsiExist i)
  have hψspec (i : Fin (C.cuspCount j)) := Classical.choose_spec (hpsiExist i)
  have hCanalytic (i : Fin (C.cuspCount j)) :
      AnalyticOnNhd ℂ (C.c j i) {s : ℂ | 0 < s.re} := C.c_analytic j i
  have hEanalytic : AnalyticOnNhd ℂ (fun s => C.componentE j s z)
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε) := by
    change AnalyticOnNhd ℂ
      (fun s => ∑ i : Fin (C.cuspCount j), C.c j i s * (C.d j i).E s z)
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε)
    exact Finset.analyticOnNhd_fun_sum Finset.univ (by
      intro i hi
      exact (hCanalytic i).mono (continuedEis_contDomain_pos C.ε C.ε_le) |>.mul (hEpoint i))
  let Ψ : ℂ → ℂ := fun s => ∑ i : Fin (C.cuspCount j), C.c j i s * ψ i s
  have hΨanalytic : AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) C.ε) := by
    apply Finset.analyticOnNhd_fun_sum
    intro i hi
    exact (hCanalytic i).mono (continuedEis_ball_pos C.ε C.ε_le) |>.mul (hψspec i).1
  have hΨcenter : Ψ (1 / 6) = C.componentTheta j z := by
    change (∑ i : Fin (C.cuspCount j), C.c j i (1 / 6) * ψ i (1 / 6)) =
      ∑ i : Fin (C.cuspCount j), C.c j i (1 / 6) * (C.d j i).res z
    apply Finset.sum_congr rfl
    intro i hi
    change C.c j i (1 / 6) * Classical.choose (hpsiExist i) (1 / 6) = _
    rw [(hψspec i).2.1]
  refine ⟨hEanalytic, ⟨Ψ, hΨanalytic, hΨcenter, ?_⟩⟩
  intro s hs hne
  change (∑ i : Fin (C.cuspCount j), C.c j i s * ψ i s) =
    (s - 1 / 6) * C.componentE j s z
  calc
    (∑ i : Fin (C.cuspCount j), C.c j i s * ψ i s) =
        ∑ i : Fin (C.cuspCount j), (s - 1 / 6) * (C.c j i s * (C.d j i).E s z) := by
          apply Finset.sum_congr rfl
          intro i hi
          change C.c j i s * Classical.choose (hpsiExist i) s = _
          rw [(hψspec i).2.2 s hs hne]
          ring
    _ = (s - 1 / 6) * C.componentE j s z := by
          simp [ContinuedEisComponents.componentE, Finset.mul_sum]

private theorem continuedEis_baseline_ball_re_gt (s : ℂ)
    (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2)) :
    (1 / 2 : ℝ) < s.re := by
  have hb := Metric.mem_ball.mp hs
  have habs : |s.re - (5 / 2 : ℝ)| < (1 / 2 : ℝ) := by
    have hle := Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
    rw [dist_eq_norm] at hb
    simpa [Complex.sub_re] using lt_of_le_of_lt hle hb
  have hlow := (abs_lt.mp habs).1
  linarith

private theorem continuedEis_component_series_formula
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I)
    (j : C.J) (s : ℂ) (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2))
    (z : ArtinPrimitiveRoots.A1.Spec.X F) :
    classicalOf P (eisenstein P G (I.sec s)) j z = C.componentE j s z := by
  have hsre := continuedEis_baseline_ball_re_gt s hs
  calc
    classicalOf P (eisenstein P G (I.sec s)) j z =
        ∑ i : Fin (C.cuspCount j), C.c j i s *
          ArtinPrimitiveRoots.A1.Spec.eisSeries F (C.Γ j) (C.σ j i) s z :=
      C.series_component j s hsre z
    _ = ∑ i : Fin (C.cuspCount j), C.c j i s * (C.d j i).E s z := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(C.d j i).E_series s hs z]
    _ = C.componentE j s z := rfl

private theorem continuedEis_eisenstein_representation
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I)
    {s : ℂ} (hs : (1 / 2 : ℝ) < s.re)
    (γ : GL (Fin 2) F) (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
    (j : C.J) (u k : P.tc.G) (hu : u ∈ infCompact P)
    (hk : k ∈ levelSet P I.T0 C.hsub C.m) :
    eisenstein P G (I.sec s)
        (P.tc.rat γ * (nInf P x * aInf P y * j) * u * k) =
      eisenstein P G (I.sec s) (nInf P x * aInf P y * j) := by
  rcases eisenstein_automorphic P G hs (I.sec s) with ⟨hAut, _, hRight⟩
  have hscalarK : ∀ h, scalarOf P G (I.sec s).f (I.sec s).fC (h * k) =
      scalarOf P G (I.sec s).f (I.sec s).fC h := fun h => C.hlevel s h k hk
  have hscalarU : ∀ h, scalarOf P G (I.sec s).f (I.sec s).fC (h * u) =
      scalarOf P G (I.sec s).f (I.sec s).fC h :=
    fun h => continuedEis_scalar_right_infCompact I s u hu h
  calc
    eisenstein P G (I.sec s) (P.tc.rat γ * (nInf P x * aInf P y * j) * u * k) =
        eisenstein P G (I.sec s) ((P.tc.rat γ * (nInf P x * aInf P y * j) * u) * k) := rfl
    _ = eisenstein P G (I.sec s) (P.tc.rat γ * (nInf P x * aInf P y * j) * u) :=
      hRight k hscalarK _
    _ = eisenstein P G (I.sec s) ((P.tc.rat γ * (nInf P x * aInf P y * j)) * u) := rfl
    _ = eisenstein P G (I.sec s) (P.tc.rat γ * (nInf P x * aInf P y * j)) :=
      hRight u hscalarU _
    _ = eisenstein P G (I.sec s) (nInf P x * aInf P y * j) := hAut γ _

private theorem continuedEis_representation_series
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I)
    {s : ℂ} (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2))
    (g : P.tc.G) (j : C.J) (γ : GL (Fin 2) F)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
    (u k : P.tc.G) (hy : ∀ w, 0 < y w) (hu : u ∈ infCompact P)
    (hk : k ∈ levelSet P I.T0 C.hsub C.m)
    (hg : g = P.tc.rat γ * (nInf P x * aInf P y * j) * u * k) :
    eisenstein P G (I.sec s) g =
      C.componentE j s (ArtinPrimitiveRoots.A1.Spec.ptX' F x y) := by
  have hsre := continuedEis_baseline_ball_re_gt s hs
  have hbase := continuedEis_eisenstein_representation C hsre γ x y j u k hu hk
  have hclass : classicalOf P (eisenstein P G (I.sec s)) j
      (ArtinPrimitiveRoots.A1.Spec.ptX' F x y) =
      eisenstein P G (I.sec s) (nInf P x * aInf P y * j) := by
    simp [classicalOf, ArtinPrimitiveRoots.A1.Spec.ptX',
      ArtinPrimitiveRoots.A1.Spec.horiz_pt, ArtinPrimitiveRoots.A1.Spec.height_pt, hy]
  calc
    eisenstein P G (I.sec s) g =
        eisenstein P G (I.sec s) (P.tc.rat γ * (nInf P x * aInf P y * j) * u * k) := by rw [hg]
    _ = eisenstein P G (I.sec s) (nInf P x * aInf P y * j) := hbase
    _ = classicalOf P (eisenstein P G (I.sec s)) j (ArtinPrimitiveRoots.A1.Spec.ptX' F x y) :=
      hclass.symm
    _ = C.componentE j s (ArtinPrimitiveRoots.A1.Spec.ptX' F x y) :=
      continuedEis_component_series_formula C j s hs _

/-- Extend the finite component cusp sums and their residues to adelic functions. The same
point representation transports both sums and the original series, and the reconstructed
functions have rational automorphy, finite-level invariance and infinite-compact invariance.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:797–808`.
Uses `continuedEis_component_unique`, `continuedEis_component_representatives`,
frozen `eisenstein_automorphic`, `scalarOf_q`,
and the component data supplied by `continuedEis_uniform_level_components`.
Consumed by series/analytic, torus-chart, smoothness parts and `exists_continuedEis`. -/
theorem continuedEis_component_reconstruction {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I) :
    Nonempty (ContinuedEisReconstruction C) := by
  classical
  choose j γ x y kinf k hy hkinf hk hg using
    (continuedEis_component_representatives C)
  let z : P.tc.G → ArtinPrimitiveRoots.A1.Spec.X F :=
    fun g => ArtinPrimitiveRoots.A1.Spec.ptX' F (x g) (y g)
  let E : ℂ → P.tc.G → ℂ := fun s g => C.componentE (j g) s (z g)
  let theta : P.tc.G → ℂ := fun g => C.componentTheta (j g) (z g)
  have hEseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ g,
      E s g = eisenstein P G (I.sec s) g := by
    intro s hs g
    dsimp [E, z]
    exact (continuedEis_representation_series C hs g (j g) (γ g) (x g) (y g)
      (kinf g) (k g) (hy g) (hkinf g) (hk g) (hg g)).symm
  have horigAut : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ γ₀ g,
      eisenstein P G (I.sec s) (P.tc.rat γ₀ * g) = eisenstein P G (I.sec s) g := by
    intro s hs γ₀ g
    exact (eisenstein_automorphic P G (continuedEis_baseline_ball_re_gt s hs)
      (I.sec s)).1 γ₀ g
  have horigLevel : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ g k₀,
      k₀ ∈ levelSet P I.T0 C.hsub C.m →
        eisenstein P G (I.sec s) (g * k₀) = eisenstein P G (I.sec s) g := by
    intro s hs g k₀ hk₀
    rcases eisenstein_automorphic P G (continuedEis_baseline_ball_re_gt s hs)
        (I.sec s) with ⟨_, _, hRight⟩
    exact hRight k₀ (fun h => C.hlevel s h k₀ hk₀) g
  have horigCompact : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ g u₀,
      u₀ ∈ infCompact P →
        eisenstein P G (I.sec s) (g * u₀) = eisenstein P G (I.sec s) g := by
    intro s hs g u₀ hu₀
    rcases eisenstein_automorphic P G (continuedEis_baseline_ball_re_gt s hs)
        (I.sec s) with ⟨_, _, hRight⟩
    exact hRight u₀ (continuedEis_scalar_right_infCompact I s u₀ hu₀) g
  have hEqCont (g g' : P.tc.G)
      (hbase : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
        eisenstein P G (I.sec s) g = eisenstein P G (I.sec s) g') :
      (Set.EqOn (E · g) (E · g')
        (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε)) ∧ theta g = theta g' := by
    have hdata := continuedEis_component_data C (j g) (z g)
    have hdata' := continuedEis_component_data C (j g') (z g')
    rcases hdata with ⟨hE, ⟨Ψ, hΨ, hΨcenter, hΨpunct⟩⟩
    rcases hdata' with ⟨hE', ⟨Ψ', hΨ', hΨcenter', hΨpunct'⟩⟩
    have hseries : Set.EqOn
        (fun s => C.componentE (j g) s (z g))
        (fun s => C.componentE (j g') s (z g'))
        (Metric.ball (5 / 2 : ℂ) (1 / 2)) := by
      intro s hs
      calc
        C.componentE (j g) s (z g) = E s g := rfl
        _ = eisenstein P G (I.sec s) g := hEseries s hs g
        _ = eisenstein P G (I.sec s) g' := hbase s hs
        _ = E s g' := (hEseries s hs g').symm
        _ = C.componentE (j g') s (z g') := rfl
    rcases continuedEis_component_unique C.ε C.ε C.ε_pos C.ε_pos
        (fun s => C.componentE (j g) s (z g))
        (fun s => C.componentE (j g') s (z g'))
        (C.componentTheta (j g) (z g)) (C.componentTheta (j g') (z g'))
        hE hE' hseries ⟨Ψ, hΨ, hΨcenter, hΨpunct⟩
        ⟨Ψ', hΨ', hΨcenter', hΨpunct'⟩ with ⟨hEq, htheta⟩
    refine ⟨?_, htheta⟩
    intro s hs
    exact hEq (by simpa using hs)
  have hEqLocal (g : P.tc.G) (j₀ : C.J) (x₀ : InfinitePlace F → ℂ)
      (y₀ : InfinitePlace F → ℝ) (hy₀ : ∀ w, 0 < y₀ w)
      (u₀ k₀ : P.tc.G) (hu₀ : u₀ ∈ infCompact P)
      (hk₀ : k₀ ∈ levelSet P I.T0 C.hsub C.m) (γ₀ : GL (Fin 2) F)
      (hg₀ : g = P.tc.rat γ₀ * (nInf P x₀ * aInf P y₀ * j₀) * u₀ * k₀) :
      (∀ s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε,
        E s g = C.componentE j₀ s (ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀)) ∧
      theta g = C.componentTheta j₀ (ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀) := by
    have hdata := continuedEis_component_data C (j g) (z g)
    have hdata' := continuedEis_component_data C j₀ (ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀)
    rcases hdata with ⟨hE, ⟨Ψ, hΨ, hΨcenter, hΨpunct⟩⟩
    rcases hdata' with ⟨hE', ⟨Ψ', hΨ', hΨcenter', hΨpunct'⟩⟩
    have hseries : Set.EqOn
        (fun s => C.componentE (j g) s (z g))
        (fun s => C.componentE j₀ s (ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀))
        (Metric.ball (5 / 2 : ℂ) (1 / 2)) := by
      intro s hs
      calc
        C.componentE (j g) s (z g) = E s g := rfl
        _ = eisenstein P G (I.sec s) g := hEseries s hs g
        _ = C.componentE j₀ s (ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀) :=
          continuedEis_representation_series C hs g j₀ γ₀ x₀ y₀ u₀ k₀ hy₀ hu₀ hk₀ hg₀
    rcases continuedEis_component_unique C.ε C.ε C.ε_pos C.ε_pos
        (fun s => C.componentE (j g) s (z g))
        (fun s => C.componentE j₀ s (ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀))
        (C.componentTheta (j g) (z g))
        (C.componentTheta j₀ (ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀))
        hE hE' hseries ⟨Ψ, hΨ, hΨcenter, hΨpunct⟩
        ⟨Ψ', hΨ', hΨcenter', hΨpunct'⟩ with ⟨hEq, htheta⟩
    exact ⟨fun s hs => hEq (by simpa using hs), htheta⟩
  have oneLevel : (1 : P.tc.G) ∈ levelSet P I.T0 C.hsub C.m := by
    refine ⟨1, by simp, ?_, ?_, ?_⟩
    · intro w
      exact map_one (P.compC w)
    · intro v hv
      simpa using (P.loc v).Kc (C.m v) |>.one_mem
    · intro v hv
      simpa using (P.tame v (fun h => hv (C.hsub h))).Kmax.one_mem
  have oneCompact : (1 : P.tc.G) ∈ infCompact P := by
    refine ⟨1, by simp, ?_, ?_⟩
    · intro v
      exact map_one (P.compF v)
    · intro w
      refine ⟨1, (Matrix.unitaryGroup (Fin 2) ℂ).one_mem, ?_⟩
      simp
  refine ⟨{
    E := E
    theta := theta
    E_aut := ?_
    E_level := ?_
    E_compact := ?_
    theta_aut := ?_
    theta_level := ?_
    theta_compact := ?_
    E_component := ?_
    theta_component := ?_
    point_transport := ?_
  }⟩
  · intro s hs γ₀ g
    exact (hEqCont (P.tc.rat γ₀ * g) g (fun t ht => horigAut t ht γ₀ g)).1 hs
  · intro s hs g k₀ hk₀
    exact (hEqCont (g * k₀) g (fun t ht => horigLevel t ht g k₀ hk₀)).1 hs
  · intro s hs g u₀ hu₀
    exact (hEqCont (g * u₀) g (fun t ht => horigCompact t ht g u₀ hu₀)).1 hs
  · intro γ₀ g
    exact (hEqCont (P.tc.rat γ₀ * g) g (fun t ht => horigAut t ht γ₀ g)).2
  · intro g k₀ hk₀
    exact (hEqCont (g * k₀) g (fun t ht => horigLevel t ht g k₀ hk₀)).2
  · intro g u₀ hu₀
    exact (hEqCont (g * u₀) g (fun t ht => horigCompact t ht g u₀ hu₀)).2
  · intro s hs j₀
    funext z₀
    let x₀ : InfinitePlace F → ℂ := fun w => ArtinPrimitiveRoots.A1.Spec.horiz (z₀ w)
    let y₀ : InfinitePlace F → ℝ := fun w => ArtinPrimitiveRoots.A1.Spec.height (z₀ w)
    have hy₀ : ∀ w, 0 < y₀ w := by
      intro w
      change 0 < ArtinPrimitiveRoots.A1.Spec.height (z₀ w)
      rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z₀ w)
    let g₀ : P.tc.G := nInf P x₀ * aInf P y₀ * j₀
    have hpt : ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀ = z₀ := by
      funext w
      exact ArtinPrimitiveRoots.A1.Spec.pt_horiz_height (z₀ w)
    have hrep : g₀ = P.tc.rat 1 * (nInf P x₀ * aInf P y₀ * j₀) * 1 * 1 := by
      simp [g₀, mul_assoc]
    have hlocal := hEqLocal g₀ j₀ x₀ y₀ hy₀ 1 1 oneCompact oneLevel 1 hrep
    calc
      classicalOf P (E s) j₀ z₀ = E s g₀ := by
        simp [classicalOf, g₀, x₀, y₀, ArtinPrimitiveRoots.A1.Spec.horiz_pt,
          ArtinPrimitiveRoots.A1.Spec.height_pt, hy₀]
      _ = C.componentE j₀ s (ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀) := hlocal.1 s hs
      _ = C.componentE j₀ s z₀ := by rw [hpt]
  · intro j₀
    funext z₀
    let x₀ : InfinitePlace F → ℂ := fun w => ArtinPrimitiveRoots.A1.Spec.horiz (z₀ w)
    let y₀ : InfinitePlace F → ℝ := fun w => ArtinPrimitiveRoots.A1.Spec.height (z₀ w)
    have hy₀ : ∀ w, 0 < y₀ w := by
      intro w
      change 0 < ArtinPrimitiveRoots.A1.Spec.height (z₀ w)
      rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z₀ w)
    let g₀ : P.tc.G := nInf P x₀ * aInf P y₀ * j₀
    have hpt : ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀ = z₀ := by
      funext w
      exact ArtinPrimitiveRoots.A1.Spec.pt_horiz_height (z₀ w)
    have hrep : g₀ = P.tc.rat 1 * (nInf P x₀ * aInf P y₀ * j₀) * 1 * 1 := by
      simp [g₀, mul_assoc]
    have hlocal := hEqLocal g₀ j₀ x₀ y₀ hy₀ 1 1 oneCompact oneLevel 1 hrep
    calc
      classicalOf P theta j₀ z₀ = theta g₀ := by
        simp [classicalOf, theta, g₀, x₀, y₀, ArtinPrimitiveRoots.A1.Spec.horiz_pt,
          ArtinPrimitiveRoots.A1.Spec.height_pt, hy₀]
      _ = C.componentTheta j₀ (ArtinPrimitiveRoots.A1.Spec.ptX' F x₀ y₀) := hlocal.2
      _ = C.componentTheta j₀ z₀ := by rw [hpt]
  · intro g
    refine ⟨j g, 1, z g, ?_, ?_, ?_⟩
    · intro s hs
      simp [E, z]
    · simp [theta, z]
    · intro s hs
      simpa using (calc
        eisenstein P G (I.sec s) g =
            C.componentE (j g) s (ArtinPrimitiveRoots.A1.Spec.ptX' F (x g) (y g)) :=
          continuedEis_representation_series C hs g (j g) (γ g) (x g) (y g)
            (kinf g) (k g) (hy g) (hkinf g) (hk g) (hg g)
        _ = classicalOf P (eisenstein P G (I.sec s)) (j g)
            (ArtinPrimitiveRoots.A1.Spec.ptX' F (x g) (y g)) :=
          (continuedEis_component_series_formula C (j g) s hs _).symm)

end ArtinPrimitiveRoots.A1.Theta
