import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

/-- Translate one already inserted local section of an analytic family. The support and
exterior sections are fixed; conjugating a common small level gives a common translated level.
Translation step.
Uses: IsSection.rtr, intertwine_rtr, the family's J_analytic and level fields.
Feeds: theta_lambda_whittaker. -/
theorem analyticFamily_rtr (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (hv0 : v0 ∈ Fam.T0) (h : (P.loc v0).L) :
    ∃ Fam' : AnalyticFamily P G μ, Fam'.T0 = Fam.T0 ∧
      (∀ s v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v) ∧
      ∀ s, (Fam'.sec s).f v0 = rtr h ((Fam.sec s).f v0) := by
  classical
  let sec' : ∀ s : ℂ, GlobalSection P G s := fun s =>
    { T0 := Fam.T0
      sub := by
        rw [← Fam.T0_eq s]
        exact (Fam.sec s).sub
      f := fun v => if hv : v = v0 then
        rtr (hv.symm ▸ h) (hv.symm ▸ (Fam.sec s).f v0) else (Fam.sec s).f v
      f_sec := by
        intro v
        by_cases hv : v = v0
        · subst v
          simp
          exact IsSection.rtr ((Fam.sec s).f_sec v0) h
        · simp only [dif_neg hv]
          exact (Fam.sec s).f_sec v
      f_sph := by
        intro v hv
        have hv0' : v ≠ v0 := by
          intro he
          subst v
          exact hv hv0
        have hvold : v ∉ (Fam.sec s).T0 := by
          simpa [Fam.T0_eq s] using hv
        obtain ⟨hval, hlevel⟩ := (Fam.sec s).f_sph v hvold
        constructor
        · simpa only [dif_neg hv0'] using hval
        · intro g k hk
          simpa only [dif_neg hv0'] using hlevel g k hk
      fC := (Fam.sec s).fC
      fC_sec := (Fam.sec s).fC_sec
      fC_smooth := (Fam.sec s).fC_smooth
      fC_jointSmooth := (Fam.sec s).fC_jointSmooth }
  let Fam' : AnalyticFamily P G μ :=
    { sec := sec'
      T0 := Fam.T0
      T0_eq := fun _ => rfl
      fC_sph := by
        intro s w
        exact Fam.fC_sph s w
      f_analytic := by
        intro v g
        by_cases hv : v = v0
        · subst v
          dsimp [sec']
          simp only [dif_pos rfl, rtr]
          exact Fam.f_analytic v0 (g * h)
        · dsimp [sec']
          simp only [dif_neg hv]
          exact Fam.f_analytic v g
      M_analytic := by
        intro v hv g
        by_cases hv0' : v = v0
        · subst v
          have heq : (fun s => intertwine (P.loc v0) (μ v0)
              (rtr h ((Fam.sec s).f v0)) g) =
              (fun s => intertwine (P.loc v0) (μ v0) ((Fam.sec s).f v0) (g * h)) := by
            funext s
            rw [intertwine_rtr]
            rfl
          dsimp [sec']
          simp
          rw [heq]
          exact Fam.M_analytic v0 hv0 (g * h)
        · have hvFam : v ∈ Fam.T0 := by simpa [hv0'] using hv
          dsimp [sec']
          simp only [dif_neg hv0']
          exact Fam.M_analytic v hvFam g
      J_analytic := by
        intro v hv g
        by_cases hv0' : v = v0
        · subst v
          have hcomp (s : ℂ) :
              rtr g (rtr h ((Fam.sec s).f v0)) = rtr (g * h) ((Fam.sec s).f v0) := by
            funext x
            simp [rtr, mul_assoc]
          have heq : (fun s => jacquet (P.loc v0) A (μ v0)
                (rtr g (rtr h ((Fam.sec s).f v0)))) =
              (fun s => jacquet (P.loc v0) A (μ v0)
                (rtr (g * h) ((Fam.sec s).f v0))) := by
            funext s
            rw [hcomp]
          dsimp [sec']
          simp
          rw [heq]
          exact Fam.J_analytic v0 hv0 (g * h)
        · have hvFam : v ∈ Fam.T0 := by simpa [hv0'] using hv
          dsimp [sec']
          simp only [dif_neg hv0']
          exact Fam.J_analytic v hvFam g
      level := by
        intro v hv
        by_cases hv0' : v = v0
        · subst v
          obtain ⟨m, hm, hlevel⟩ := Fam.level v0 hv0
          let U : Set (P.loc v0).L := {k | h⁻¹ * k * h ∈ (P.loc v0).Kc m}
          have hcont : Continuous (fun k : (P.loc v0).L => h⁻¹ * k * h) := by fun_prop
          have hUopen : IsOpen U := by
            change IsOpen ((fun k : (P.loc v0).L => h⁻¹ * k * h) ⁻¹'
              ((P.loc v0).Kc m : Set (P.loc v0).L))
            exact (P.loc v0).Kc_open m hm |>.preimage hcont
          have hUone : (1 : (P.loc v0).L) ∈ U := by simp [U]
          obtain ⟨m', hm', hmsub⟩ :=
            (P.loc v0).Kc_nhds U (hUopen.mem_nhds hUone)
          refine ⟨m', hm', ?_⟩
          intro s g k hk
          dsimp [sec']
          simp [rtr]
          have harg : (g * k) * h = (g * h) * (h⁻¹ * k * h) := by group
          rw [harg]
          exact hlevel s (g * h) (h⁻¹ * k * h) (hmsub hk)
        · have hvFam : v ∈ Fam.T0 := by simpa [hv0'] using hv
          obtain ⟨m, hm, hlevel⟩ := Fam.level v hvFam
          refine ⟨m, hm, ?_⟩
          intro s g k hk
          dsimp [sec']
          simp only [dif_neg hv0']
          exact hlevel s g k hk }
  refine ⟨Fam', rfl, ?_, ?_⟩
  · intro s v hv
    dsimp [Fam', sec']
    simp only [dif_neg hv]
  · intro s
    dsimp [Fam', sec']
    simp

end ArtinPrimitiveRoots.A1.Theta
