import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

private theorem intertwine_add_smul_of_isSection {v : FinPlace F}
    (L : FinLocalCover D H v) (T : TorusRep D H v) (μ : LocHaar v)
    (s : ℂ) (hs : 0 < s.re) (f₁ f₂ : L.L → T.V)
    (hf₁ : IsSection L T s f₁) (hf₂ : IsSection L T s f₂) (c : ℂ) :
    intertwine L μ (f₁ + c • f₂) = intertwine L μ f₁ + c • intertwine L μ f₂ := by
  funext g
  have h₁ := (intertwine_isSection L T μ s hs f₁ hf₁).1 g
  have h₂ := (intertwine_isSection L T μ s hs f₂ hf₂).1 g
  simp only [intertwine, Pi.add_apply, Pi.smul_apply]
  change (∫ x, f₁ (L.w * L.n (Multiplicative.ofAdd x) * g) +
      (c • fun x => f₂ (L.w * L.n (Multiplicative.ofAdd x) * g)) x ∂μ.μ) = _
  rw [MeasureTheory.integral_add h₁ (MeasureTheory.Integrable.smul c h₂)]
  congr 1
  change (∫ x, c • f₂ (L.w * L.n (Multiplicative.ofAdd x) * g) ∂μ.μ) = _
  rw [MeasureTheory.integral_smul]

/-- Form a local affine linear combination of two families with the same exterior sections.
The resulting family has the same inserted support and a common small level.
Guide: sol-thin-thglobal/PROOFS.md:915–929.
Uses: sectionSpace closure, intertwine_isSection (integrability), jacquet_linear.
Feeds: theta_lambda_descent and thetaWhit_section_multilinear. -/
theorem analyticFamily_add_smul (Fam : AnalyticFamily P G μ) (v0 : FinPlace F)
    (Fam₁ Fam₂ : AnalyticFamily P G μ) (h₁ : ExteriorFamily Fam v0 Fam₁)
    (h₂ : ExteriorFamily Fam v0 Fam₂) (c : ℂ) :
    ∃ Fam₃ : AnalyticFamily P G μ, ExteriorFamily Fam v0 Fam₃ ∧
      ∀ s, (Fam₃.sec s).f v0 = (Fam₁.sec s).f v0 + c • (Fam₂.sec s).f v0 := by
  classical
  let sec' : ∀ s : ℂ, GlobalSection P G s := fun s =>
    { T0 := insert v0 Fam.T0
      sub := fun x hx => Finset.mem_insert_of_mem (by
        simpa [Fam.T0_eq s] using (Fam.sec s).sub hx)
      f := fun v => if hv : v = v0 then
        hv.symm ▸ ((Fam₁.sec s).f v0 + c • (Fam₂.sec s).f v0) else (Fam.sec s).f v
      f_sec := by
        intro v
        by_cases hv : v = v0
        · subst v
          simp
          change (Fam₁.sec s).f v0 + c • (Fam₂.sec s).f v0 ∈
            sectionSpace (P.loc v0) (G.T v0) s
          have hsec₁ : (Fam₁.sec s).f v0 ∈ sectionSpace (P.loc v0) (G.T v0) s :=
            by
              change IsSection (P.loc v0) (G.T v0) s ((Fam₁.sec s).f v0)
              exact (Fam₁.sec s).f_sec v0
          have hsec₂ : (Fam₂.sec s).f v0 ∈ sectionSpace (P.loc v0) (G.T v0) s :=
            by
              change IsSection (P.loc v0) (G.T v0) s ((Fam₂.sec s).f v0)
              exact (Fam₂.sec s).f_sec v0
          exact (sectionSpace (P.loc v0) (G.T v0) s).add_mem hsec₁
            ((sectionSpace (P.loc v0) (G.T v0) s).smul_mem c hsec₂)
        · simpa [hv] using (Fam.sec s).f_sec v
      f_sph := by
        intro v hv
        have hvne : v ≠ v0 := by
          intro he
          subst v
          exact hv (Finset.mem_insert_self v0 Fam.T0)
        have hvFam : v ∉ Fam.T0 := by
          intro hv'
          exact hv (Finset.mem_insert_of_mem hv')
        have hvold : v ∉ (Fam.sec s).T0 := by
          simpa [Fam.T0_eq s] using hvFam
        obtain ⟨hval, hlevel⟩ := (Fam.sec s).f_sph v hvold
        constructor
        · simpa [hvne] using hval
        · intro g k hk
          simpa [hvne] using hlevel g k hk
      fC := (Fam.sec s).fC
      fC_sec := (Fam.sec s).fC_sec
      fC_smooth := (Fam.sec s).fC_smooth
      fC_jointSmooth := (Fam.sec s).fC_jointSmooth }
  have hsec0 (s : ℂ) : (sec' s).f v0 =
      (Fam₁.sec s).f v0 + c • (Fam₂.sec s).f v0 := by
    simp [sec']
  have hv₁ : v0 ∈ Fam₁.T0 := by
    rw [h₁.1]
    exact Finset.mem_insert_self v0 Fam.T0
  have hv₂ : v0 ∈ Fam₂.T0 := by
    rw [h₂.1]
    exact Finset.mem_insert_self v0 Fam.T0
  let Fam₃ : AnalyticFamily P G μ :=
    { sec := sec'
      T0 := insert v0 Fam.T0
      T0_eq := fun _ => rfl
      fC_sph := by
        intro s w
        exact Fam.fC_sph s w
      f_analytic := by
        intro v g
        by_cases hv : v = v0
        · subst v
          have hEq : (fun s => (sec' s).f v0 g) =
              (fun s => (Fam₁.sec s).f v0 g + c • (Fam₂.sec s).f v0 g) := by
            funext s
            exact congrFun (hsec0 s) g
          rw [hEq]
          exact (Fam₁.f_analytic v0 g).add ((Fam₂.f_analytic v0 g).const_smul)
        · have hEq : (fun s => (sec' s).f v g) =
              (fun s => (Fam.sec s).f v g) := by
            funext s
            simp [sec', hv]
          rw [hEq]
          exact Fam.f_analytic v g
      M_analytic := by
        intro v hv g
        by_cases hv0' : v = v0
        · subst v
          have hEq : {s : ℂ | 0 < s.re}.EqOn
              (fun s => intertwine (P.loc v0) (μ v0) ((sec' s).f v0) g)
              (fun s => intertwine (P.loc v0) (μ v0) ((Fam₁.sec s).f v0) g +
                c • intertwine (P.loc v0) (μ v0) ((Fam₂.sec s).f v0) g) := by
            intro s hs
            change intertwine (P.loc v0) (μ v0) ((sec' s).f v0) g = _
            rw [hsec0 s]
            exact congrFun (intertwine_add_smul_of_isSection
              (P.loc v0) (G.T v0) (μ v0) s hs
              ((Fam₁.sec s).f v0) ((Fam₂.sec s).f v0)
              ((Fam₁.sec s).f_sec v0) ((Fam₂.sec s).f_sec v0) c) g
          have hbase := (Fam₁.M_analytic v0 hv₁ g).add
            ((Fam₂.M_analytic v0 hv₂ g).const_smul (c := c))
          exact hbase.congr (isOpen_lt continuous_const Complex.continuous_re) (by
            intro s hs
            exact (hEq hs).symm)
        · have hvFam : v ∈ Fam.T0 := by
            rcases Finset.mem_insert.mp hv with h | h
            · exact (hv0' h).elim
            · exact h
          have hEq : (fun s => intertwine (P.loc v) (μ v) ((sec' s).f v) g) =
              (fun s => intertwine (P.loc v) (μ v) ((Fam.sec s).f v) g) := by
            funext s
            simp [sec', hv0']
          rw [hEq]
          exact Fam.M_analytic v hvFam g
      J_analytic := by
        intro v hv g
        by_cases hv0' : v = v0
        · subst v
          have hEq : (fun s => jacquet (P.loc v0) A (μ v0)
                (rtr g ((sec' s).f v0))) =
              (fun s => jacquet (P.loc v0) A (μ v0)
                (rtr g ((Fam₁.sec s).f v0)) +
                c • jacquet (P.loc v0) A (μ v0) (rtr g ((Fam₂.sec s).f v0))) := by
            funext s
            change jacquet (P.loc v0) A (μ v0) (rtr g ((sec' s).f v0)) = _
            rw [hsec0 s]
            rw [show rtr g ((Fam₁.sec s).f v0 + c • (Fam₂.sec s).f v0) =
                rtr g ((Fam₁.sec s).f v0) + c • rtr g ((Fam₂.sec s).f v0) by
                  funext x
                  simp [rtr]]
            exact jacquet_linear (P.loc v0) (G.T v0) A (μ v0) s
              (rtr g ((Fam₁.sec s).f v0)) (rtr g ((Fam₂.sec s).f v0))
              (IsSection.rtr ((Fam₁.sec s).f_sec v0) g)
              (IsSection.rtr ((Fam₂.sec s).f_sec v0) g) c
          have hbase := (Fam₁.J_analytic v0 hv₁ g).add
            ((Fam₂.J_analytic v0 hv₂ g).const_smul (c := c))
          exact hbase.congr (isOpen_lt continuous_const Complex.continuous_re) (by
            intro s hs
            exact (congrFun hEq s).symm)
        · have hvFam : v ∈ Fam.T0 := by
            rcases Finset.mem_insert.mp hv with h | h
            · exact (hv0' h).elim
            · exact h
          have hEq : (fun s => jacquet (P.loc v) A (μ v)
                (rtr g ((sec' s).f v))) =
              (fun s => jacquet (P.loc v) A (μ v)
                (rtr g ((Fam.sec s).f v))) := by
            funext s
            simp [sec', hv0']
          rw [hEq]
          exact Fam.J_analytic v hvFam g
      level := by
        intro v hv
        by_cases hv0' : v = v0
        · subst v
          obtain ⟨m₁, hm₁, hlevel₁⟩ := Fam₁.level v0 hv₁
          obtain ⟨m₂, hm₂, hlevel₂⟩ := Fam₂.level v0 hv₂
          refine ⟨max m₁ m₂, le_trans hm₁ (Nat.le_max_left _ _), ?_⟩
          intro s g k hk
          have hk₁ : k ∈ (P.loc v0).Kc m₁ :=
            (P.loc v0).Kc_anti m₁ (max m₁ m₂) hm₁ (Nat.le_max_left _ _) hk
          have hk₂ : k ∈ (P.loc v0).Kc m₂ :=
            (P.loc v0).Kc_anti m₂ (max m₁ m₂) hm₂ (Nat.le_max_right _ _) hk
          rw [hsec0 s]
          change (Fam₁.sec s).f v0 (g * k) + c • (Fam₂.sec s).f v0 (g * k) = _
          simp only [Pi.add_apply, Pi.smul_apply]
          rw [hlevel₁ s g k hk₁, hlevel₂ s g k hk₂]
        · have hvFam : v ∈ Fam.T0 := by
            rcases Finset.mem_insert.mp hv with h | h
            · exact (hv0' h).elim
            · exact h
          obtain ⟨m, hm, hlevel⟩ := Fam.level v hvFam
          refine ⟨m, hm, ?_⟩
          intro s g k hk
          dsimp [sec']
          simp [hv0']
          exact hlevel s g k hk }
  refine ⟨Fam₃, ?_, ?_⟩
  · constructor
    · rfl
    · intro s v hv
      dsimp [Fam₃, sec']
      simp [hv]
  · intro s
    exact hsec0 s

end ArtinPrimitiveRoots.A1.Theta
