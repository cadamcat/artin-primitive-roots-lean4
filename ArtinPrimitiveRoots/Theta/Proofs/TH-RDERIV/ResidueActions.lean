import ArtinPrimitiveRoots.Theta.Res

set_option autoImplicit false

open NumberField IsDedekindDomain Module MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem residue_ball_re_gt_half (s : ℂ)
    (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2)) :
    1 / 2 < s.re := by
  have hdist : dist s (5 / 2 : ℂ) < 1 / 2 := Metric.mem_ball.mp hs
  have hnorm : ‖s - (5 / 2 : ℂ)‖ < 1 / 2 := by
    simpa [dist_eq_norm] using hdist
  have hreal : |s.re - (5 / 2 : ℝ)| < 1 / 2 := by
    have hle := Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
    simpa [Complex.sub_re] using lt_of_le_of_lt hle hnorm
  have hlow := (abs_lt.mp hreal).1
  linarith

private theorem section_right_Kext {P : CoverPackage D S H A}
    {G : GlobalDatum P} {s : ℂ} (Fs : GlobalSection P G s)
    (hT : Fs.T0 = S.Sf) (g k : P.tc.G) (hk : k ∈ P.tc.Kext) :
    scalarOf P G Fs.f Fs.fC (g * k) = scalarOf P G Fs.f Fs.fC g := by
  classical
  obtain ⟨y, hy, hyK, hyS, hyC⟩ := P.Kext_components k hk
  obtain ⟨x, hx⟩ := P.q_surj g
  have hxy : P.q (x * y) = g * k := by
    rw [map_mul, hx, hy]
  have hleft := (scalarOf_q P G Fs (x * y)).2
  have hright := (scalarOf_q P G Fs x).2
  rw [hxy] at hleft
  rw [hx] at hright
  have hF :
      (fun v : FinPlace F => G.lam v (Fs.f v (P.compF v (x * y)))) =
        (fun v : FinPlace F => G.lam v (Fs.f v (P.compF v x))) := by
    funext v
    rw [map_mul]
    by_cases hv : v ∈ S.Sf
    · rw [hyS v hv, mul_one]
    · have hvT : v ∉ Fs.T0 := by rwa [hT]
      rw [(Fs.f_sph v hvT).2 (P.compF v x) (P.compF v y) (hyK v hv)]
  have hC : (∏ w : InfinitePlace F, Fs.fC w (P.compC w (x * y))) =
      ∏ w : InfinitePlace F, Fs.fC w (P.compC w x) := by
    apply Finset.prod_congr rfl
    intro w _
    rw [map_mul, hyC w, mul_one]
  rw [hleft, hright, hF, hC]

private theorem residue_series_symmetry {P : CoverPackage D S H A}
    {G : GlobalDatum P} {μ : ∀ v : FinPlace F, LocHaar v}
    (Fam : AnalyticFamily P G μ) (C : ContinuedEis Fam) (g g' : P.tc.G) (q : ℂ)
    (hSeries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      C.E s g' = q * C.E s g) : C.theta g' = q * C.theta g := by
  exact analytic_residue_unique C.ε C.ε_pos
    (fun s => C.E s g') (fun s => C.E s g) (C.theta g') (C.theta g) q
    (C.E_analytic g') (C.E_analytic g) (C.laurent g') (C.laurent g) hSeries

theorem theta_residue_actions {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) :
    (∀ γ g, C.theta (P.tc.rat γ * g) = C.theta g) ∧
    (∀ ζ g, C.theta (P.tc.z ζ * g) = ((ζ : ℂˣ) : ℂ) * C.theta g) ∧
    (Fam.T0 = S.Sf → ∀ g, ∀ k ∈ P.tc.Kext, C.theta (g * k) = C.theta g) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro γ g
    have h := residue_series_symmetry Fam C g (P.tc.rat γ * g) 1 (by
      intro s hs
      rw [C.E_series s hs (P.tc.rat γ * g), C.E_series s hs g]
      simpa only [one_mul] using
        (eisenstein_automorphic P G (residue_ball_re_gt_half s hs) (Fam.sec s)).1 γ g)
    simpa only [one_mul] using h
  · intro ζ g
    apply residue_series_symmetry Fam C g (P.tc.z ζ * g) ((ζ : ℂˣ) : ℂ)
    intro s hs
    rw [C.E_series s hs (P.tc.z ζ * g), C.E_series s hs g]
    exact (eisenstein_automorphic P G (residue_ball_re_gt_half s hs) (Fam.sec s)).2.1 ζ g
  · intro hT g k hk
    have h := residue_series_symmetry Fam C g (g * k) 1 (by
      intro s hs
      rw [C.E_series s hs (g * k), C.E_series s hs g]
      have hfix : ∀ h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k) =
          scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
        intro h
        exact section_right_Kext (Fam.sec s) ((Fam.T0_eq s).trans hT) h k hk
      simpa only [one_mul] using
        (eisenstein_automorphic P G (residue_ball_re_gt_half s hs) (Fam.sec s)).2.2 k hfix g)
    simpa only [one_mul] using h

end ArtinPrimitiveRoots.Proofs.thsol_torusf
