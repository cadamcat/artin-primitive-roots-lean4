import ArtinPrimitiveRoots.Proofs.th_res_whit_b.LambdaCore

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

/-- Realize an arbitrary tuple of local `s0` sections by one analytic family, leaving all
finite components outside `S.Sf` equal to the base family. -/
theorem analyticFamily_realize_section_tuple (Fam : AnalyticFamily P G μ)
    (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6))
    (g : P.tc.G) (laws : ThetaResidueLaws P G μ) :
    ∃ F' : AnalyticFamily P G μ, F'.T0 = Fam.T0 ∧
      (∀ v : S.Sf, (F'.sec (1 / 6)).f v.1 = f v) ∧
      (∀ s v, v ∉ S.Sf → (F'.sec s).f v = (Fam.sec s).f v) := by
  classical
  have hrec : ∀ t : Finset S.Sf, ∃ F' : AnalyticFamily P G μ, F'.T0 = Fam.T0 ∧
      (∀ v ∈ t, (F'.sec (1 / 6)).f v.1 = f v) ∧
      (∀ s v, v ∉ S.Sf → (F'.sec s).f v = (Fam.sec s).f v) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        refine ⟨Fam, rfl, ?_, ?_⟩
        · intro v hv
          simp at hv
        · intro s v hv
          rfl
    | @insert v t hv ih =>
        obtain ⟨F₀, hT₀, hcoord₀, hOff₀⟩ := ih
        obtain ⟨F₁, hExt, hAt⟩ := analyticFamily_realize_section F₀ v.1
          (f v).1 (f v).2 g laws
        have hvTbase : v.1 ∈ Fam.T0 := by
          rw [← Fam.T0_eq (1 / 6)]
          exact (Fam.sec (1 / 6)).sub v.2
        have hvT : v.1 ∈ F₀.T0 := by rw [hT₀]; exact hvTbase
        have hT₁ : F₁.T0 = Fam.T0 := by
          calc
            F₁.T0 = insert v.1 F₀.T0 := hExt.1
            _ = Fam.T0 := by rw [hT₀, Finset.insert_eq_of_mem hvTbase]
        refine ⟨F₁, hT₁, ?_, ?_⟩
        · intro w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with rfl | hw
          · exact hAt
          · have hwv : w.1 ≠ v.1 := by
              intro heq
              apply hv
              exact Subtype.ext heq ▸ hw
            calc
              (F₁.sec (1 / 6)).f w.1 = (F₀.sec (1 / 6)).f w.1 :=
                hExt.2 (1 / 6) w.1 hwv
              _ = f w := hcoord₀ w hw
        · intro s w hw
          have hwv : w ≠ v.1 := by
            intro heq
            exact hw (heq ▸ v.2)
          calc
            (F₁.sec s).f w = (F₀.sec s).f w := hExt.2 s w hwv
            _ = (Fam.sec s).f w := hOff₀ s w hw
  obtain ⟨F', hT, hcoord, hOff⟩ := hrec Finset.univ
  refine ⟨F', hT, ?_, hOff⟩
  intro v
  exact hcoord v (by simp)

/-- The theta residue coefficient only depends on the family sections at s0 and the fixed
exterior family data. -/
theorem thetaWhit_eq_of_section_family_realizers (Fam₁ Fam₂ : AnalyticFamily P G μ)
    (C₁ : ContinuedEis Fam₁) (C₂ : ContinuedEis Fam₂)
    (hT : Fam₁.T0 = Fam₂.T0)
    (hcoord : ∀ v : S.Sf, (Fam₁.sec (1 / 6)).f v.1 = (Fam₂.sec (1 / 6)).f v.1)
    (hOff : ∀ s v, v ∉ S.Sf → (Fam₁.sec s).f v = (Fam₂.sec s).f v)
    (g : P.tc.G) (laws : ThetaResidueLaws P G μ) :
    thetaWhit C₁ g = thetaWhit C₂ g := by
  have hM : ∀ v ∈ Fam₁.T0,
      intertwine (P.loc v) (μ v) ((Fam₁.sec (1 / 6)).f v) =
        intertwine (P.loc v) (μ v) ((Fam₂.sec (1 / 6)).f v) := by
    intro v hv
    by_cases hvS : v ∈ S.Sf
    · let vS : S.Sf := ⟨v, hvS⟩
      exact congrArg (intertwine (P.loc v) (μ v)) (hcoord vS)
    · exact congrArg (intertwine (P.loc v) (μ v)) (hOff (1 / 6) v hvS)
  have hθ := laws.dependsOnM Fam₁ Fam₂ C₁ C₂ hT hM
  exact thetaWhit_eq_of_theta_eq Fam₁ Fam₂ C₁ C₂ g laws hθ

/-- Choose an adelic representative with the prescribed finite components off `S.Sf`, identity
components at `S.Sf`, and identity complex components. -/
theorem exists_section_referenceRP (x0 : P.RP) :
    ∃ x : P.RP, (∀ v : S.Sf, P.compF v.1 x = 1) ∧
      (∀ v, v ∉ S.Sf → P.compF v x = P.compF v x0) ∧
      (∀ w, P.compC w x = 1) := by
  classical
  let lf : ∀ v : FinPlace F, (P.loc v).L := fun v =>
    if hv : v ∈ S.Sf then 1 else P.compF v x0
  have hfinite : Set.Finite {v : FinPlace F | ∃ hv : v ∉ S.Sf,
      lf v ∉ (P.tame v hv).Kmax} := by
    apply (P.comp_restricted x0).subset
    intro v hv
    rcases hv with ⟨hvS, hnot⟩
    have hlf : lf v = P.compF v x0 := by simp [lf, hvS]
    exact ⟨hvS, by rw [← hlf]; exact hnot⟩
  obtain ⟨x, hcomp⟩ := P.comp_surj lf (fun _ => 1) hfinite
  refine ⟨x, ?_, ?_, ?_⟩
  · intro v
    simpa [lf, v.2] using hcomp.1 v.1
  · intro v hv
    simpa [lf, hv] using hcomp.1 v
  · exact hcomp.2

noncomputable def sectionReferenceRP (x0 : P.RP) : P.RP :=
  Classical.choose (exists_section_referenceRP x0)

theorem sectionReferenceRP_spec (x0 : P.RP) :
    (∀ v : S.Sf, P.compF v.1 (sectionReferenceRP x0) = 1) ∧
      (∀ v, v ∉ S.Sf → P.compF v (sectionReferenceRP x0) = P.compF v x0) ∧
      (∀ w, P.compC w (sectionReferenceRP x0) = 1) :=
  Classical.choose_spec (exists_section_referenceRP x0)

noncomputable def sectionFamilyRealizer (Fam : AnalyticFamily P G μ) (x0 : P.RP)
    (laws : ThetaResidueLaws P G μ)
    (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) :
    AnalyticFamily P G μ :=
  Classical.choose (analyticFamily_realize_section_tuple Fam f
    (P.q (sectionReferenceRP x0)) laws)

theorem sectionFamilyRealizer_spec (Fam : AnalyticFamily P G μ) (x0 : P.RP)
    (laws : ThetaResidueLaws P G μ)
    (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) :
    (sectionFamilyRealizer Fam x0 laws f).T0 = Fam.T0 ∧
      (∀ v, ((sectionFamilyRealizer Fam x0 laws f).sec (1 / 6)).f v.1 = f v) ∧
      (∀ s v, v ∉ S.Sf →
        ((sectionFamilyRealizer Fam x0 laws f).sec s).f v = (Fam.sec s).f v) :=
  Classical.choose_spec (analyticFamily_realize_section_tuple Fam f
    (P.q (sectionReferenceRP x0)) laws)

noncomputable def sectionFamilyContinuation (laws : ThetaResidueLaws P G μ)
    (Fam : AnalyticFamily P G μ) : ContinuedEis Fam :=
  Classical.choice (laws.continuation Fam)

noncomputable def sectionResidueValue (Fam : AnalyticFamily P G μ) (x0 : P.RP)
    (laws : ThetaResidueLaws P G μ)
    (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) : ℂ :=
  thetaWhit (sectionFamilyContinuation laws (sectionFamilyRealizer Fam x0 laws f))
    (P.q (sectionReferenceRP x0))

/-- The embedded root subgroup at one place of S is the corresponding coordinate in the
global S-unipotent. -/
theorem section_local_n_eq_nS (v : S.Sf) (t : v.1.adicCompletion F) :
    P.emb v.1 ((P.loc v.1).n (Multiplicative.ofAdd t)) =
      P.tc.nS (Multiplicative.ofAdd ((Function.update
        (fun w : S.Sf => (0 : w.1.adicCompletion F)) v t, fun _ => 0) : S.FS)) := by
  classical
  let u : S.FS := (Function.update (fun w : S.Sf => (0 : w.1.adicCompletion F)) v t,
    fun _ => 0)
  have hupper0 : upperM ℂ (0 : ℂ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperM]
  obtain ⟨y, hyq, hyF, hyC⟩ := P.nS_components u
  have hxy : P.incl v.1 ((P.loc v.1).n (Multiplicative.ofAdd t)) = y := by
    apply P.comp_ext
    · intro w
      by_cases hw : w = v.1
      · subst w
        rw [P.incl_compF, hyF]
        simp [u]
      · rw [P.incl_compF_other v.1 w (Ne.symm hw), hyF]
        by_cases hws : w ∈ S.Sf
        · have hne : (⟨w, hws⟩ : S.Sf) ≠ v := by
            intro heq
            apply hw
            exact congrArg Subtype.val heq
          simp [u, hws, hne, Function.update]
        · simp [u, hws]
    · intro w
      rw [P.incl_compC, hyC]
      have hzero : upperM ℂ (u.2 w) = 1 := by simpa [u] using hupper0
      rw [hzero]
      simp
  calc
    P.emb v.1 ((P.loc v.1).n (Multiplicative.ofAdd t)) =
        P.q (P.incl v.1 ((P.loc v.1).n (Multiplicative.ofAdd t))) := by
          rw [P.q_incl]
    _ = P.q y := congrArg P.q hxy
    _ = P.tc.nS (Multiplicative.ofAdd u) := hyq

/-- The global additive character on a tuple supported at one S-place reduces to its local
character there. -/
theorem section_e_single (v : S.Sf) (t : v.1.adicCompletion F) :
    S.e A ((Function.update (fun w : S.Sf => (0 : w.1.adicCompletion F)) v t,
      fun _ => 0) : S.FS) = A.ψ v.1 t := by
  classical
  let u : S.FS := (Function.update (fun w : S.Sf => (0 : w.1.adicCompletion F)) v t,
    fun _ => 0)
  have huAt : u.1 v = t := by simp [u, Function.update]
  have huOff : ∀ w : S.Sf, w ≠ v → A.ψ w.1 (u.1 w) = 1 := by
    intro w hne
    have hw : u.1 w = 0 := by simp [u, Function.update, hne]
    simp [hw]
  have hprod : (∏ w : S.Sf, A.ψ w.1 (u.1 w)) = A.ψ v.1 t := by
    rw [Fintype.prod_eq_single v]
    · simpa [huAt]
    · intro w hne
      exact huOff w hne
  unfold SData.e
  change (∏ w : S.Sf, A.ψ w.1 (u.1 w)) *
      (∏ w : InfinitePlace F, psiC (u.2 w)) = A.ψ v.1 t
  rw [hprod]
  simp [u, psiC]

/-- A reference representative with identity component at v commutes with the local embedding. -/
theorem sectionReference_commute (xStar : P.RP)
    (hStarS : ∀ v : S.Sf, P.compF v.1 xStar = 1)
    (hStarC : ∀ w, P.compC w xStar = 1) (v : S.Sf) (h : (P.loc v.1).L) :
    xStar * P.incl v.1 h = P.incl v.1 h * xStar := by
  apply P.comp_ext
  · intro w
    simp only [map_mul]
    by_cases hw : w = v.1
    · subst w
      rw [hStarS]
      simp
    · rw [P.incl_compF_other v.1 w (Ne.symm hw)]
      simp
  · intro w
    simp [P.incl_compC, hStarC]

/-- Define the finite-place residue functional from families realizing arbitrary local sections.
Its well-definedness and separate additivity/scalar compatibility use residue dependence on the
intertwined s0 sections and affine family linearity. -/
theorem thetaWhit_section_residue_form (Fam : AnalyticFamily P G μ) (x0 : P.RP)
    (laws : ThetaResidueLaws P G μ) :
    ∃ W : MultilinearMap ℂ
        (fun v : S.Sf => sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) ℂ,
      (∀ (v : S.Sf) (f : ∀ w : S.Sf, sectionSpace (P.loc w.1) (G.T w.1) (1 / 6))
        (t : v.1.adicCompletion F),
        W (Function.update f v (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6)
          ((P.loc v.1).n (Multiplicative.ofAdd t)) (f v))) = A.ψ v.1 t * W f) ∧
      ∀ f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6),
        W f = sectionResidueValue Fam x0 laws f := by
  classical
  let xStar := sectionReferenceRP x0
  have hStar := sectionReferenceRP_spec x0
  have hStarS := hStar.1
  have hStarOff := hStar.2.1
  have hStarC := hStar.2.2
  let raw (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) := f
  let realize (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) :
      AnalyticFamily P G μ := sectionFamilyRealizer Fam x0 laws (raw f)
  have hrealize (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) :
      (realize f).T0 = Fam.T0 ∧
        (∀ v, ((realize f).sec (1 / 6)).f v.1 = (raw f) v) ∧
        (∀ s v, v ∉ S.Sf → ((realize f).sec s).f v = (Fam.sec s).f v) :=
    sectionFamilyRealizer_spec Fam x0 laws (raw f)
  let cont (F' : AnalyticFamily P G μ) : ContinuedEis F' :=
    sectionFamilyContinuation laws F'
  let value (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) : ℂ :=
    sectionResidueValue Fam x0 laws (raw f)
  have hValue (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6))
      (F' : AnalyticFamily P G μ) (hT : F'.T0 = Fam.T0)
      (hcoord : ∀ v, ((F'.sec (1 / 6)).f v.1 = (raw f) v))
      (hOff : ∀ s v, v ∉ S.Sf → (F'.sec s).f v = (Fam.sec s).f v) :
      value f = thetaWhit (cont F') (P.q xStar) := by
    have hT' : (realize f).T0 = F'.T0 := (hrealize f).1.trans hT.symm
    have hcoord' : ∀ v : S.Sf,
        ((realize f).sec (1 / 6)).f v.1 = (F'.sec (1 / 6)).f v.1 := by
      intro v
      exact ((hrealize f).2.1 v).trans (hcoord v).symm
    have hOff' : ∀ s v, v ∉ S.Sf →
        ((realize f).sec s).f v = (F'.sec s).f v := by
      intro s v hv
      exact ((hrealize f).2.2 s v hv).trans (hOff s v hv).symm
    exact thetaWhit_eq_of_section_family_realizers (realize f) F'
      (cont (realize f)) (cont F') hT' hcoord' hOff' (P.q xStar) laws
  have hRawAdd (f : ∀ w : S.Sf, sectionSpace (P.loc w.1) (G.T w.1) (1 / 6))
      (v : S.Sf) (x y : sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) :
      (raw (Function.update f v (x + y))) v =
        (raw (Function.update f v x)) v + (raw (Function.update f v y)) v := by
    simp [raw, Function.update]
  have hRawSmul (f : ∀ w : S.Sf, sectionSpace (P.loc w.1) (G.T w.1) (1 / 6))
      (v : S.Sf) (c : ℂ) (x : sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) :
      (raw (Function.update f v (c • x))) v = c • (raw (Function.update f v x)) v := by
    simp [raw, Function.update]
  have hvFamT (v : S.Sf) : v.1 ∈ Fam.T0 := by
    rw [← Fam.T0_eq (1 / 6)]
    exact (Fam.sec (1 / 6)).sub v.2
  have hFamilyInput
      (fbase : ∀ w : S.Sf, sectionSpace (P.loc w.1) (G.T w.1) (1 / 6))
      (B : AnalyticFamily P G μ) (hBT : B.T0 = Fam.T0)
      (hBCoord : ∀ w, (B.sec (1 / 6)).f w.1 = (raw fbase) w)
      (hBOff : ∀ s w, w ∉ S.Sf → (B.sec s).f w = (Fam.sec s).f w)
      (v : S.Sf) (z : sectionSpace (P.loc v.1) (G.T v.1) (1 / 6))
      (F' : AnalyticFamily P G μ) (hExt : ExteriorFamily B v.1 F')
      (hAt : (F'.sec (1 / 6)).f v.1 = (raw (Function.update fbase v z)) v) :
      value (Function.update fbase v z) = thetaWhit (cont F') (P.q xStar) := by
    have hT : F'.T0 = Fam.T0 := by
      calc
        F'.T0 = insert v.1 B.T0 := hExt.1
        _ = Fam.T0 := by rw [hBT]; exact Finset.insert_eq_of_mem (hvFamT v)
    have hcoord : ∀ w, (F'.sec (1 / 6)).f w.1 =
        (raw (Function.update fbase v z)) w := by
      intro w
      by_cases hw : w = v
      · subst w
        exact hAt
      · calc
          (F'.sec (1 / 6)).f w.1 = (B.sec (1 / 6)).f w.1 := hExt.2 (1 / 6) w.1 (by
            intro heq
            apply hw
            exact Subtype.ext heq)
          _ = (raw fbase) w := hBCoord w
          _ = (raw (Function.update fbase v z)) w := by
            simp [raw, Function.update, hw]
    have hOff : ∀ s w, w ∉ S.Sf → (F'.sec s).f w = (Fam.sec s).f w := by
      intro s w hw
      have hwv : w ≠ v.1 := by intro heq; exact hw (heq ▸ v.2)
      calc
        (F'.sec s).f w = (B.sec s).f w := hExt.2 s w hwv
        _ = (Fam.sec s).f w := hBOff s w hw
    exact hValue (Function.update fbase v z) F' hT hcoord hOff
  have hAdd : ∀ (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6))
      (v : S.Sf) (x y : sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)),
      value (Function.update f v (x + y)) =
        value (Function.update f v x) + value (Function.update f v y) := by
    intro f v x y
    let f₀ := Function.update f v (0 : sectionSpace (P.loc v.1) (G.T v.1) (1 / 6))
    let B := realize f₀
    have hB := hrealize f₀
    obtain ⟨X, hXext, hXat⟩ := analyticFamily_realize_section B v.1 x.1 x.2
      (P.q xStar) laws
    obtain ⟨Y, hYext, hYat⟩ := analyticFamily_realize_section B v.1 y.1 y.2
      (P.q xStar) laws
    have hvT : v.1 ∈ B.T0 := by
      rw [hB.1]
      exact hvFamT v
    have hBself : ExteriorFamily B v.1 B := by
      refine ⟨(Finset.insert_eq_of_mem hvT).symm, ?_⟩
      intro s w hw
      rfl
    rcases analyticFamily_add_smul B v.1 X Y hXext hYext 1 with
      ⟨H', hHext, hHcomb⟩
    let CX := cont X
    let CY := cont Y
    let CH := cont H'
    have hXtuple : value (Function.update f v x) = thetaWhit CX (P.q xStar) := by
      apply hValue (Function.update f v x) X ?_ ?_ ?_
      · calc
          X.T0 = insert v.1 B.T0 := hXext.1
          _ = Fam.T0 := by rw [hB.1]; exact Finset.insert_eq_of_mem (hvFamT v)
      · intro w
        by_cases hw : w = v
        · subst w
          simpa [raw, Function.update] using hXat
        · calc
            (X.sec (1 / 6)).f w.1 = (B.sec (1 / 6)).f w.1 := hXext.2 (1 / 6) w.1 (by
              intro heq
              apply hw
              exact Subtype.ext heq)
            _ = (raw f₀) w := hB.2.1 w
            _ = (raw (Function.update f v x)) w := by
              simp [raw, f₀, Function.update, hw]
      · intro s w hw
        have hwv : w ≠ v.1 := by intro heq; exact hw (heq ▸ v.2)
        calc
          (X.sec s).f w = (B.sec s).f w := hXext.2 s w hwv
          _ = (Fam.sec s).f w := hB.2.2 s w hw
    have hYtuple : value (Function.update f v y) = thetaWhit CY (P.q xStar) := by
      apply hValue (Function.update f v y) Y ?_ ?_ ?_
      · calc
          Y.T0 = insert v.1 B.T0 := hYext.1
          _ = Fam.T0 := by rw [hB.1]; exact Finset.insert_eq_of_mem (hvFamT v)
      · intro w
        by_cases hw : w = v
        · subst w
          simpa [raw, Function.update] using hYat
        · calc
            (Y.sec (1 / 6)).f w.1 = (B.sec (1 / 6)).f w.1 := hYext.2 (1 / 6) w.1 (by
              intro heq
              apply hw
              exact Subtype.ext heq)
            _ = (raw f₀) w := hB.2.1 w
            _ = (raw (Function.update f v y)) w := by
              simp [raw, f₀, Function.update, hw]
      · intro s w hw
        have hwv : w ≠ v.1 := by intro heq; exact hw (heq ▸ v.2)
        calc
          (Y.sec s).f w = (B.sec s).f w := hYext.2 s w hwv
          _ = (Fam.sec s).f w := hB.2.2 s w hw
    have hHtuple : value (Function.update f v (x + y)) = thetaWhit CH (P.q xStar) := by
      apply hValue (Function.update f v (x + y)) H' ?_ ?_ ?_
      · calc
          H'.T0 = insert v.1 B.T0 := hHext.1
          _ = Fam.T0 := by rw [hB.1]; exact Finset.insert_eq_of_mem (hvFamT v)
      · intro w
        by_cases hw : w = v
        · subst w
          have hsum : (H'.sec (1 / 6)).f v.1 =
              (raw (Function.update f v x)) v + (raw (Function.update f v y)) v := by
            calc
              (H'.sec (1 / 6)).f v.1 = (X.sec (1 / 6)).f v.1 +
                  (Y.sec (1 / 6)).f v.1 := by simpa using hHcomb (1 / 6)
              _ = (raw (Function.update f v x)) v +
                  (raw (Function.update f v y)) v := by
                    rw [hXat, hYat]
                    simp [raw, Function.update]
          exact hsum.trans (congrArg Subtype.val (hRawAdd f v x y).symm)
        · calc
            (H'.sec (1 / 6)).f w.1 = (B.sec (1 / 6)).f w.1 := hHext.2 (1 / 6) w.1 (by
              intro heq
              apply hw
              exact Subtype.ext heq)
            _ = (raw f₀) w := hB.2.1 w
            _ = (raw (Function.update f v (x + y))) w := by
              simp [raw, f₀, Function.update, hw]
      · intro s w hw
        have hwv : w ≠ v.1 := by intro heq; exact hw (heq ▸ v.2)
        calc
          (H'.sec s).f w = (B.sec s).f w := hHext.2 s w hwv
          _ = (Fam.sec s).f w := hB.2.2 s w hw
    have hlin := (laws.linearTranslate v.1 X Y H' CX CY CH).1
      (by
        intro s w hw
        have hwv : w ≠ v.1 := hw
        exact ⟨(hYext.2 s w hwv).trans (hXext.2 s w hwv).symm,
          (hHext.2 s w hwv).trans (hXext.2 s w hwv).symm⟩)
      (1 : ℂ) hHcomb
    have hθ := thetaWhit_linear_common_domain X Y H' CX CY CH (P.q xStar) laws 1 hlin
    rw [hHtuple, hXtuple, hYtuple]
    simpa using hθ
  have hValueZero : ∀ (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6))
      (v : S.Sf), value (Function.update f v 0) = 0 := by
    intro f v
    let f₀ := Function.update f v (0 : sectionSpace (P.loc v.1) (G.T v.1) (1 / 6))
    let B := realize f₀
    have hB := hrealize f₀
    have hvT : v.1 ∈ B.T0 := by rw [hB.1]; exact hvFamT v
    let φ : v.1.adicCompletion F → (G.T v.1).V := fun _ => 0
    have hφ : IsLocallyConstant φ := IsLocallyConstant.const 0
    have hφc : HasCompactSupport φ := by
      apply HasCompactSupport.of_support_subset_isCompact isCompact_empty
      intro z hz
      simp [φ] at hz
    obtain ⟨Z, hZext, hZcoord⟩ := analyticFamily_bigCell_rtr B v.1 φ hφ hφc 1
    have hZzero : ∀ s, (Z.sec s).f v.1 = 0 := by
      intro s
      funext z
      rw [hZcoord s]
      simp [rtr, bigCell, φ]
    have hRaw0 : (raw (Function.update f₀ v 0)) v = 0 := by
      simp [raw, f₀, Function.update]
    have hZat : (Z.sec (1 / 6)).f v.1 = (raw (Function.update f₀ v 0)) v := by
      simpa [hRaw0] using hZzero (1 / 6)
    have hZvalue := hFamilyInput f₀ B hB.1 hB.2.1 hB.2.2 v 0 Z hZext hZat
    calc
      value (Function.update f v 0) = thetaWhit (cont Z) (P.q xStar) := by
        simpa [f₀] using hZvalue
      _ = 0 := thetaWhit_zero_local_family v.1 Z hZzero (P.q xStar) laws (cont Z)
  have hSmul : ∀ (f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6))
      (v : S.Sf) (c : ℂ) (x : sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)),
      value (Function.update f v (c • x)) = c * value (Function.update f v x) := by
    intro f v c x
    let f₀ := Function.update f v (0 : sectionSpace (P.loc v.1) (G.T v.1) (1 / 6))
    let B := realize f₀
    have hB := hrealize f₀
    have hvT : v.1 ∈ B.T0 := by rw [hB.1]; exact hvFamT v
    have hBself : ExteriorFamily B v.1 B := by
      refine ⟨(Finset.insert_eq_of_mem hvT).symm, ?_⟩
      intro s w hw
      rfl
    obtain ⟨X, hXext, hXat⟩ := analyticFamily_realize_section B v.1 x.1 x.2
      (P.q xStar) laws
    obtain ⟨H', hHext, hHcomb⟩ := analyticFamily_add_smul B v.1 B X hBself hXext c
    let CB := cont B
    let CX := cont X
    let CH := cont H'
    have hXat0 : (X.sec (1 / 6)).f v.1 = (raw (Function.update f₀ v x)) v := by
      simpa [raw, f₀, Function.update] using hXat
    have hXtuple' := hFamilyInput f₀ B hB.1 hB.2.1 hB.2.2 v x X hXext hXat0
    have hXtuple : value (Function.update f v x) = thetaWhit CX (P.q xStar) := by
      simpa [f₀, Function.update] using hXtuple'
    have hRawZero : (raw f₀) v = 0 := by
      simp [raw, f₀, Function.update]
    have hRawX₀ : (raw (Function.update f₀ v x)) v = x := by
      simp [raw, f₀, Function.update]
    have hRawCX₀ : (raw (Function.update f₀ v (c • x))) v = c • x := by
      rw [hRawSmul f₀ v c x, hRawX₀]
    have hHat₀ : (H'.sec (1 / 6)).f v.1 =
        (raw (Function.update f₀ v (c • x))) v := by
      calc
        (H'.sec (1 / 6)).f v.1 = (B.sec (1 / 6)).f v.1 +
            c • (X.sec (1 / 6)).f v.1 := hHcomb (1 / 6)
        _ = (raw f₀) v + c • x := by rw [hB.2.1 v, hXat0, hRawX₀]
        _ = (raw (Function.update f₀ v (c • x))) v := by
          rw [hRawZero, hRawCX₀]
          simp
    have hHtuple : value (Function.update f v (c • x)) = thetaWhit CH (P.q xStar) := by
      have h := hFamilyInput f₀ B hB.1 hB.2.1 hB.2.2 v (c • x) H' hHext hHat₀
      simpa [f₀, Function.update] using h
    have hlin := (laws.linearTranslate v.1 B X H' CB CX CH).1
      (by
        intro s w hw
        have hwv : w ≠ v.1 := hw
        exact ⟨(hXext.2 s w hwv).trans (hBself.2 s w hwv).symm,
          (hHext.2 s w hwv).trans (hBself.2 s w hwv).symm⟩)
      c hHcomb
    have hθ := thetaWhit_linear_common_domain B X H' CB CX CH (P.q xStar) laws c hlin
    calc
      value (Function.update f v (c • x)) = thetaWhit CH (P.q xStar) := hHtuple
      _ = thetaWhit CB (P.q xStar) +
          c • thetaWhit CX (P.q xStar) := hθ
      _ = c * value (Function.update f v x) := by
        have hCBzero : thetaWhit CB (P.q xStar) = 0 := by
          have hBvalue : value f₀ = thetaWhit CB (P.q xStar) :=
            hValue f₀ B hB.1 hB.2.1 hB.2.2
          calc
            thetaWhit CB (P.q xStar) = value f₀ := hBvalue.symm
            _ = 0 := by simpa [f₀] using hValueZero f v
        rw [hCBzero]
        simp only [zero_add, smul_eq_mul]
        rw [← hXtuple]
  let W : MultilinearMap ℂ
      (fun v : S.Sf => sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) ℂ :=
    MultilinearMap.mk' value hAdd (by
      intro f v c x
      simpa only [smul_eq_mul] using hSmul f v c x)
  refine ⟨W, ?_, ?_⟩
  · intro v f t
    let Ffam := realize f
    have hF := hrealize f
    have hvT : v.1 ∈ Ffam.T0 := by rw [hF.1]; exact hvFamT v
    let n := (P.loc v.1).n (Multiplicative.ofAdd t)
    obtain ⟨F', hT', hOff', hAt'⟩ := analyticFamily_rtr Ffam v.1 hvT n
    let CF := cont Ffam
    let CF' := cont F'
    have hFcoord : (Ffam.sec (1 / 6)).f v.1 = f v := by
      simpa [raw] using hF.2.1 v
    have hcoord : ∀ w, (F'.sec (1 / 6)).f w.1 =
        (raw (Function.update f v (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6) n (f v)))) w := by
      intro w
      by_cases hw : w = v
      · subst w
        rw [hAt' (1 / 6)]
        simpa [raw, sectionRtr, Function.update, hFcoord]
      · have hwv : w.1 ≠ v.1 := by
          intro heq
          apply hw
          exact Subtype.ext heq
        calc
          (F'.sec (1 / 6)).f w.1 = (Ffam.sec (1 / 6)).f w.1 := hOff' (1 / 6) w.1 hwv
          _ = (raw f) w := hF.2.1 w
          _ = (raw (Function.update f v
              (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6) n (f v)))) w := by
                simp [raw, Function.update, hw]
    have hOff : ∀ s w, w ∉ S.Sf → (F'.sec s).f w = (Fam.sec s).f w := by
      intro s w hw
      have hwv : w ≠ v.1 := by intro heq; exact hw (heq ▸ v.2)
      calc
        (F'.sec s).f w = (Ffam.sec s).f w := hOff' s w hwv
        _ = (Fam.sec s).f w := hF.2.2 s w hw
    have hValueTranslate := hValue
      (Function.update f v (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6) n (f v)))
      F' (by rw [hT', hF.1]) hcoord hOff
    have htranslate := thetaWhit_translate_family Ffam F' v.1 n hOff' hAt' CF CF'
      (P.q xStar) laws
    have hcommRP := sectionReference_commute xStar hStarS hStarC v n
    have hcomm : P.q xStar * P.emb v.1 n = P.emb v.1 n * P.q xStar := by
      have h := congrArg P.q hcommRP
      simpa [map_mul, P.q_incl] using h
    let u : S.FS :=
      (Function.update (fun w : S.Sf => (0 : w.1.adicCompletion F)) v t, fun _ => 0)
    have hN : P.emb v.1 n = P.tc.nS (Multiplicative.ofAdd u) := by
      simpa [n, u, Function.update] using section_local_n_eq_nS v t
    have hE : S.e A u = A.ψ v.1 t := by
      simpa [u, Function.update] using section_e_single v t
    calc
      W (Function.update f v
        (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6) n (f v))) =
          thetaWhit CF' (P.q xStar) := hValueTranslate
      _ = thetaWhit CF (P.q xStar * P.emb v.1 n) := htranslate
      _ = thetaWhit CF (P.emb v.1 n * P.q xStar) := by rw [hcomm]
      _ = thetaWhit CF (P.tc.nS (Multiplicative.ofAdd u) * P.q xStar) := by rw [hN]
      _ = S.e A u * thetaWhit CF (P.q xStar) := (laws.equiv Ffam CF).2.1 u (P.q xStar)
      _ = A.ψ v.1 t * W f := by rw [hE]; rfl
  · intro f
    simp [W, value, sectionResidueValue, raw]

end ArtinPrimitiveRoots.A1.Theta
