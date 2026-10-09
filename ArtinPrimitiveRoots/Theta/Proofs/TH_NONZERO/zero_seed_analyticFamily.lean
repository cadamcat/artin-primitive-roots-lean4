import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.sphC_right_root_smooth
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.spherical_section_param_analytic

set_option autoImplicit false
open NumberField IsDedekindDomain
open Filter
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem spherical_left_root_invariant (s x : ℂ) (g : PGL2 ℂ) :
    sphC s (nC x * g) = sphC s g := by
  have hdiag : diagM ℂ 1 = (1 : GL (Fin 2) ℂ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagM]
  simpa [hdiag, nC] using (sphC_isSection s).1 x 1 g

private theorem spherical_joint_root_smooth (s : ℂ) (g : PGL2 ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℂ => sphC s (nC p.1 * g * nC p.2)) := by
  have heq : (fun p : ℂ × ℂ => sphC s (nC p.1 * g * nC p.2)) =
      fun p => sphC s (g * nC p.2) := by
    funext p
    rw [mul_assoc, spherical_left_root_invariant]
  rw [heq]
  simpa only [Function.comp_def] using (sphC_right_root_smooth s g).comp contDiff_snd

private theorem seed_jacquet_zero {v : FinPlace F} (L : FinLocalCover D H v)
    (T : TorusRep D H v) (A : AddCharData F) (μ : LocHaar v) :
    jacquet L A μ (0 : L.L → T.V) = 0 := by
  have hzero : (fun N : ℕ => jacquetTrunc L A μ N (0 : L.L → T.V)) =
      fun _ => (0 : T.V) := by
    funext N
    simp [jacquetTrunc]
  unfold jacquet
  rw [hzero]
  exact tendsto_const_nhds.limUnder_eq

/-- A spherical analytic family whose exceptional finite sections are all zero. -/
theorem zero_seed_analyticFamily (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) :
    ∃ Fam : AnalyticFamily P G μ, Fam.T0 = S.Sf ∧
      ∀ v ∈ S.Sf, ∀ s : ℂ, (Fam.sec s).f v = 0 := by
  let sec' : ∀ s : ℂ, GlobalSection P G s := fun s =>
    { T0 := S.Sf
      sub := fun _ h => h
      f := fun v => if hv : v ∈ S.Sf then 0 else
        (spherical_section (P.loc v) (P.tame v hv) (G.T v) (G.B v hv)
          (fun h => hv (S.over6 v h)) s).choose
      f_sec := by
        intro v
        by_cases hv : v ∈ S.Sf
        · simp only [dite_eq_left hv]
          refine ⟨?_, ?_, ⟨(P.loc v).m0, le_rfl, ?_⟩⟩
          · intro x y g
            simp
          · intro ζ g
            simp
          · intro g k hk
            rfl
        · simpa only [dite_eq_right hv] using
            (spherical_section (P.loc v) (P.tame v hv) (G.T v) (G.B v hv)
              (fun h => hv (S.over6 v h)) s).choose_spec.1
      f_sph := by
        intro v hv
        have hf := (spherical_section (P.loc v) (P.tame v hv) (G.T v) (G.B v hv)
          (fun h => hv (S.over6 v h)) s).choose_spec
        simpa only [dite_eq_right hv] using And.intro hf.2.1 hf.2.2.1
      fC := fun _ => sphC s
      fC_sec := fun _ => sphC_isSection s
      fC_smooth := fun _ g => sphC_right_root_smooth s g
      fC_jointSmooth := fun _ g => spherical_joint_root_smooth s g }
  have hzero (s : ℂ) (v : FinPlace F) (hv : v ∈ S.Sf) : (sec' s).f v = 0 := by
    simp [sec', hv]
  let Fam' : AnalyticFamily P G μ :=
    { sec := sec'
      T0 := S.Sf
      T0_eq := fun _ => rfl
      fC_sph := fun _ _ => rfl
      f_analytic := by
        intro v g
        by_cases hv : v ∈ S.Sf
        · have heq : (fun s => (sec' s).f v g) = fun _ => (0 : (G.T v).V) := by
            funext s
            rw [hzero s v hv]
            rfl
          rw [heq]
          exact analyticOnNhd_const
        · have heq : (fun s => (sec' s).f v g) = fun s =>
              (spherical_section (P.loc v) (P.tame v hv) (G.T v) (G.B v hv)
                (fun h => hv (S.over6 v h)) s).choose g := by
            funext s
            simp [sec', hv]
          rw [heq]
          exact spherical_section_param_analytic (P.loc v) (P.tame v hv) (G.T v)
            (G.B v hv) (fun h => hv (S.over6 v h)) g
      M_analytic := by
        intro v hv g
        have heq : (fun s => intertwine (P.loc v) (μ v) ((sec' s).f v) g) =
            fun _ => (0 : (G.T v).V) := by
          funext s
          rw [hzero s v hv]
          simp [intertwine]
        rw [heq]
        exact analyticOnNhd_const
      J_analytic := by
        intro v hv g
        have heq : (fun s => jacquet (P.loc v) A (μ v) (rtr g ((sec' s).f v))) =
            fun _ => (0 : (G.T v).V) := by
          funext s
          rw [hzero s v hv]
          change jacquet (P.loc v) A (μ v) (0 : (P.loc v).L → (G.T v).V) = 0
          exact seed_jacquet_zero (P.loc v) (G.T v) A (μ v)
        rw [heq]
        exact analyticOnNhd_const
      level := by
        intro v hv
        refine ⟨(P.loc v).m0, le_rfl, ?_⟩
        intro s g k hk
        rw [hzero s v hv]
        rfl }
  refine ⟨Fam', rfl, ?_⟩
  intro v hv s
  exact hzero s v hv

end ArtinPrimitiveRoots.A1.Theta
