import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_unique

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {CE : ℕ} {condη : Ideal (𝓞 F)}
  {S : SData F CE condη} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

/-- An affine identity between Eisenstein series passes to their residues
by uniqueness of scalar analytic continuation. -/
theorem residue_affine (Fam Fam' Fam'' : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) (C' : ContinuedEis Fam') (C'' : ContinuedEis Fam'')
    (c : ℂ) (hseries : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2), ∀ g,
      eisenstein P G (Fam''.sec s) g =
        eisenstein P G (Fam.sec s) g + c * eisenstein P G (Fam'.sec s) g) :
    C''.theta = C.theta + c • C'.theta := by
  funext g
  change C''.theta g = C.theta g + c * C'.theta g
  let δ : ℝ := min C.ε C'.ε
  have hδpos : 0 < δ := lt_min C.ε_pos C'.ε_pos
  have hδε : δ ≤ C.ε := min_le_left _ _
  have hδε' : δ ≤ C'.ε := min_le_right _ _
  have hdom (ε : ℝ) (hδ : δ ≤ ε) :
      ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) δ ⊆
        ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε := by
    intro s hs
    simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hs ⊢
    rcases hs with (ha | hb) | hc
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr hb)
    · exact Or.inr ⟨Metric.ball_subset_ball hδ hc.1, hc.2⟩
  have hE : AnalyticOnNhd ℂ (fun s => C.E s g + c * C'.E s g)
      (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) δ) := by
    exact ((C.E_analytic g).mono (hdom C.ε hδε)).add
      ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => c) _).mul
        ((C'.E_analytic g).mono (hdom C'.ε hδε')))
  have hlaurent : ∃ Ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) δ) ∧
      Ψ (1 / 6) = C.theta g + c * C'.theta g ∧
      ∀ s ∈ Metric.ball (1 / 6 : ℂ) δ, s ≠ 1 / 6 →
        Ψ s = (s - 1 / 6) * (C.E s g + c * C'.E s g) := by
    obtain ⟨Ψ, hΨ, hΨcenter, hΨvalue⟩ := C.laurent g
    obtain ⟨Ψ', hΨ', hΨ'center, hΨ'value⟩ := C'.laurent g
    refine ⟨fun s => Ψ s + c * Ψ' s, ?_, ?_, ?_⟩
    · exact (hΨ.mono (Metric.ball_subset_ball hδε)).add
        ((analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => c) _).mul
          (hΨ'.mono (Metric.ball_subset_ball hδε')))
    · change Ψ (1 / 6) + c * Ψ' (1 / 6) = C.theta g + c * C'.theta g
      rw [hΨcenter, hΨ'center]
    · intro s hs hsne
      change Ψ s + c * Ψ' s = (s - 1 / 6) * (C.E s g + c * C'.E s g)
      rw [hΨvalue s (Metric.ball_subset_ball hδε hs) hsne,
        hΨ'value s (Metric.ball_subset_ball hδε' hs) hsne]
      ring
  have hseries' : Set.EqOn (fun s => C''.E s g)
      (fun s => C.E s g + c * C'.E s g) (Metric.ball (5 / 2 : ℂ) (1 / 2)) := by
    intro s hs
    change C''.E s g = C.E s g + c * C'.E s g
    rw [C''.E_series s hs, C.E_series s hs, C'.E_series s hs]
    exact hseries s hs g
  exact (continuedEis_component_unique C''.ε δ C''.ε_pos hδpos
    (fun s => C''.E s g) (fun s => C.E s g + c * C'.E s g)
    (C''.theta g) (C.theta g + c * C'.theta g)
    (C''.E_analytic g) hE hseries' (C''.laurent g) hlaurent).2

end ArtinPrimitiveRoots.A1.Theta
