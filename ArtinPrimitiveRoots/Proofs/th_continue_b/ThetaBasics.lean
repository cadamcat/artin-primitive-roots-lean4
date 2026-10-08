import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_representatives

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 128
open NumberField IsDedekindDomain
open scoped Classical ContDiff MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem continuedEis_componentTheta_contDiffOn
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I) (j : C.J) :
    ContDiffOn ℝ ∞
      (fun p : ArtinPrimitiveRoots.A1.Spec.Coord F =>
        C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F p))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
  have hsum : ContDiffOn ℝ ∞
      (fun p : ArtinPrimitiveRoots.A1.Spec.Coord F =>
        ∑ i, C.c j i (1 / 6) * (C.d j i).res (ArtinPrimitiveRoots.A1.Spec.ptX F p))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) := by
    apply ContDiffOn.sum
    intro i hi
    exact contDiffOn_const.mul (C.d j i).res_smooth
  simpa [ContinuedEisComponents.componentTheta] using hsum

theorem continuedEis_matrixMul_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x => B x i j)) :
    ∀ i j, ContDiff ℝ ∞ (fun x => (A x * B x) i j) := by
  intro i j
  change ContDiff ℝ ∞ (fun x => ∑ k : Fin 2, A x i k * B x k j)
  apply ContDiff.sum
  intro k hk
  exact (hA i k).mul (hB k j)

noncomputable def continuedEis_slLiftPGL (g : PGL2 ℂ) : SL(2, ℂ) := by
  have hroots : ∀ r : ℂˣ, ∃ k : ℂˣ, k ^ Fintype.card (Fin 2) = r := by
    intro r
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (r : ℂ) (by norm_num : 0 < Fintype.card (Fin 2))
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num : Fintype.card (Fin 2) ≠ 0)] at hz
      exact (r.ne_zero) hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    apply Units.ext
    change z ^ Fintype.card (Fin 2) = (r : ℂ)
    exact hz
  let hsurj := Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots
    (n := Fin 2) (R := ℂ) hroots
  let x := Classical.choose (hsurj g)
  have hx : Matrix.ProjectiveSpecialLinearGroup.toPGL x = g :=
    Classical.choose_spec (hsurj g)
  let s : SL(2, ℂ) := Classical.choose (QuotientGroup.mk_surjective x)
  exact s

theorem continuedEis_slLiftPGL_toPGL (g : PGL2 ℂ) :
    Matrix.SpecialLinearGroup.toPGL (continuedEis_slLiftPGL g) = g := by
  classical
  dsimp [continuedEis_slLiftPGL]
  let hroots : ∀ r : ℂˣ, ∃ k : ℂˣ, k ^ Fintype.card (Fin 2) = r := by
    intro r
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (r : ℂ) (by norm_num : 0 < Fintype.card (Fin 2))
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num : Fintype.card (Fin 2) ≠ 0)] at hz
      exact (r.ne_zero) hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    apply Units.ext
    change z ^ Fintype.card (Fin 2) = (r : ℂ)
    exact hz
  let hsurj := Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots
    (n := Fin 2) (R := ℂ) hroots
  let x := Classical.choose (hsurj g)
  have hx : Matrix.ProjectiveSpecialLinearGroup.toPGL x = g :=
    Classical.choose_spec (hsurj g)
  let s : SL(2, ℂ) := Classical.choose (QuotientGroup.mk_surjective x)
  have hs : (QuotientGroup.mk s :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) = x :=
    Classical.choose_spec (QuotientGroup.mk_surjective x)
  have h' : Matrix.ProjectiveSpecialLinearGroup.toPGL
      (QuotientGroup.mk s : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) = g := by
    rw [hs, hx]
  simpa only [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk] using h'

theorem continuedEis_slFixBase_unitary (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F]
    (g : SL(2, ℂ))
    (hg : g • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  obtain ⟨_, _, _, hherm, _, _, _, _, _, _, _, _⟩ :=
    ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F)
  have hbaseMat : ArtinPrimitiveRoots.A1.Spec.ptMat (0 : ℂ) (1 : ℝ)
      (by norm_num) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ArtinPrimitiveRoots.A1.Spec.ptMat]
  have hpt0 : ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      (QuotientGroup.mk (1 : SL(2, ℂ)) : ArtinPrimitiveRoots.A1.Spec.H3) := by
    simp [ArtinPrimitiveRoots.A1.Spec.pt, hbaseMat]
  have hbase : ArtinPrimitiveRoots.A1.Spec.herm
      (ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) = 1 := by
    rw [hpt0]
    simp [ArtinPrimitiveRoots.A1.Spec.herm]
  have h := congrArg ArtinPrimitiveRoots.A1.Spec.herm hg
  rw [hherm g (ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)), hbase] at h
  exact Matrix.mem_unitaryGroup_iff.mpr (by simpa using h)

theorem continuedEis_ptMat_smul_base (x : ℂ) (y : ℝ) (hy : 0 < y) :
    ArtinPrimitiveRoots.A1.Spec.ptMat x y hy •
        ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      ArtinPrimitiveRoots.A1.Spec.pt x y := by
  have hbaseMat : ArtinPrimitiveRoots.A1.Spec.ptMat (0 : ℂ) (1 : ℝ)
      (by norm_num) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ArtinPrimitiveRoots.A1.Spec.ptMat]
  have hpt0 : ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      (QuotientGroup.mk (1 : SL(2, ℂ)) : ArtinPrimitiveRoots.A1.Spec.H3) := by
    simp [ArtinPrimitiveRoots.A1.Spec.pt, hbaseMat]
  rw [hpt0]
  simp [ArtinPrimitiveRoots.A1.Spec.pt, hy]

theorem continuedEis_ptMat_pgl (x : ℂ) (y : ℝ) (hy : 0 < y) :
    (QuotientGroup.mk
      (ArtinPrimitiveRoots.A1.Spec.ptMat x y hy : GL (Fin 2) ℂ) : PGL2 ℂ) =
      (QuotientGroup.mk
        (upperM ℂ x * diagM ℂ (Units.mk0 (y : ℂ)
          (Complex.ofReal_ne_zero.mpr hy.ne')) : GL (Fin 2) ℂ) : PGL2 ℂ) := by
  have hsqrt : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hroot : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast hsqrt.ne'
  change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (Real.sqrt y : ℂ) hroot, ?_⟩
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.diagonal, Matrix.scalar, ArtinPrimitiveRoots.A1.Spec.ptMat,
      upperM, diagM, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar, Complex.ofReal_mul,
      Real.mul_self_sqrt hy.le]
    <;> field_simp [hroot]
    <;> norm_num [Real.mul_self_sqrt hy.le]
    <;> rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt hy.le]

def continuedEis_baseDen (g : SL(2, ℂ)) : ℝ :=
  Complex.normSq (g 1 0) + Complex.normSq (g 1 1)

def continuedEis_baseNum (g : SL(2, ℂ)) : ℂ :=
  g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1)

def continuedEis_baseCoord (g : SL(2, ℂ)) : ℂ × ℝ :=
  (continuedEis_baseNum g / (continuedEis_baseDen g : ℂ),
    (continuedEis_baseDen g)⁻¹)

theorem continuedEis_baseDen_pos (g : SL(2, ℂ)) :
    0 < continuedEis_baseDen g := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  by_cases h0 : g 1 0 = 0
  · have h1 : g 1 1 ≠ 0 := by
      intro h1
      rw [h0, h1] at hdet
      simp at hdet
    simp only [continuedEis_baseDen, h0, Complex.normSq_zero, zero_add]
    exact Complex.normSq_pos.mpr h1
  · unfold continuedEis_baseDen
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr h0)
      (le_add_of_nonneg_right (Complex.normSq_nonneg _))

theorem continuedEis_coords_base_action (g : SL(2, ℂ)) :
    ArtinPrimitiveRoots.A1.Spec.coordsX F
      (fun _ : InfinitePlace F => g • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) =
    fun _ => continuedEis_baseCoord g := by
  obtain ⟨_, _, _, hherm, _, _, _, _, _, _, _, _⟩ :=
    ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F)
  have hbaseMat : ArtinPrimitiveRoots.A1.Spec.ptMat (0 : ℂ) (1 : ℝ)
      (by norm_num) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ArtinPrimitiveRoots.A1.Spec.ptMat]
  have hpt0 : ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      (QuotientGroup.mk (1 : SL(2, ℂ)) : ArtinPrimitiveRoots.A1.Spec.H3) := by
    simp [ArtinPrimitiveRoots.A1.Spec.pt, hbaseMat]
  have hbase : ArtinPrimitiveRoots.A1.Spec.herm
      (ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) = 1 := by
    rw [hpt0]
    simp [ArtinPrimitiveRoots.A1.Spec.herm]
  have hmul : ArtinPrimitiveRoots.A1.Spec.herm
      (g • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hherm, hbase]
    simp
  have h01 : ArtinPrimitiveRoots.A1.Spec.herm
      (g • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) 0 1 =
      continuedEis_baseNum g := by
    rw [hmul]
    simp [continuedEis_baseNum, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_apply]
  have h11 : ArtinPrimitiveRoots.A1.Spec.herm
      (g • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) 1 1 =
      (continuedEis_baseDen g : ℂ) := by
    rw [hmul]
    simp [continuedEis_baseDen, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_apply, Complex.normSq_eq_conj_mul_self, Complex.ofReal_add]
    ring
  funext w
  simp only [ArtinPrimitiveRoots.A1.Spec.coordsX, ArtinPrimitiveRoots.A1.Spec.horiz,
    ArtinPrimitiveRoots.A1.Spec.height]
  rw [h01, h11]
  simp [continuedEis_baseCoord, continuedEis_baseDen_pos]

theorem continuedEis_baseCoord_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (M : E → SL(2, ℂ))
    (hM : ∀ i j, ContDiff ℝ ∞ (fun q => M q i j)) :
    ContDiff ℝ ∞ (fun q => continuedEis_baseCoord (M q)) := by
  have hnormSq : ContDiff ℝ ∞ (Complex.normSq : ℂ → ℝ) := by
    change ContDiff ℝ ∞ (fun z : ℂ => Complex.reCLM z * Complex.reCLM z +
      Complex.imCLM z * Complex.imCLM z)
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hD0 : ContDiff ℝ ∞ (fun q => Complex.normSq (M q 1 0)) :=
    hnormSq.comp (hM 1 0)
  have hD1 : ContDiff ℝ ∞ (fun q => Complex.normSq (M q 1 1)) :=
    hnormSq.comp (hM 1 1)
  have hden : ContDiff ℝ ∞ (fun q => continuedEis_baseDen (M q)) := by
    simpa [continuedEis_baseDen] using hD0.add hD1
  have hnum : ContDiff ℝ ∞ (fun q => continuedEis_baseNum (M q)) := by
    have hc0 : ContDiff ℝ ∞ (fun q => star (M q 1 0)) :=
      Complex.conjCLE.contDiff.comp (hM 1 0)
    have hc1 : ContDiff ℝ ∞ (fun q => star (M q 1 1)) :=
      Complex.conjCLE.contDiff.comp (hM 1 1)
    simpa [continuedEis_baseNum] using
      (hM 0 0).mul hc0 |>.add ((hM 0 1).mul hc1)
  have hden_ne : ∀ q, continuedEis_baseDen (M q) ≠ 0 :=
    fun q => (continuedEis_baseDen_pos (M q)).ne'
  have hden_inv : ContDiff ℝ ∞ (fun q => (continuedEis_baseDen (M q))⁻¹) :=
    hden.inv hden_ne
  have hdenC : ContDiff ℝ ∞
      (fun q => ((continuedEis_baseDen (M q) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hden
  have hdenC_inv : ContDiff ℝ ∞
      (fun q => ((continuedEis_baseDen (M q) : ℝ) : ℂ)⁻¹) :=
    hdenC.inv (fun q => Complex.ofReal_ne_zero.mpr (hden_ne q))
  have hfirst : ContDiff ℝ ∞ (fun q =>
      continuedEis_baseNum (M q) / (continuedEis_baseDen (M q) : ℂ)) := by
    simpa only [div_eq_mul_inv] using hnum.mul hdenC_inv
  change ContDiff ℝ ∞ (fun q =>
    (continuedEis_baseNum (M q) / (continuedEis_baseDen (M q) : ℂ),
      (continuedEis_baseDen (M q))⁻¹))
  exact hfirst.prodMk hden_inv

noncomputable def continuedEis_conjugateRoot
    (γ : GL (Fin 2) ℂ) (z : ℂ) : SL(2, ℂ) :=
  ⟨((γ⁻¹ * upperM ℂ z * γ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), by
    have hu : Matrix.GeneralLinearGroup.det (upperM ℂ z) = 1 := by
      apply Units.ext
      simp [upperM, Matrix.det_fin_two]
    have hdet : Matrix.GeneralLinearGroup.det
        (γ⁻¹ * upperM ℂ z * γ : GL (Fin 2) ℂ) = 1 := by
      simp [map_mul, map_inv, hu]
    simpa [Matrix.GeneralLinearGroup.det] using
      congrArg (fun u : ℂˣ => (u : ℂ)) hdet⟩

theorem continuedEis_conjugateRoot_toGL (γ : GL (Fin 2) ℂ) (z : ℂ) :
    Matrix.SpecialLinearGroup.toGL (continuedEis_conjugateRoot γ z) =
      γ⁻¹ * upperM ℂ z * γ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

noncomputable def continuedEis_rootRep {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) : P.RP :=
  Classical.choose (P.nS_components ((fun _ : S.Sf => (0 : _), x)))

theorem continuedEis_rootRep_q {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) :
    P.q (continuedEis_rootRep P x) = nInf P x := by
  change P.q (Classical.choose (P.nS_components ((fun _ : S.Sf => (0 : _), x)))) = _
  rw [(Classical.choose_spec (P.nS_components ((fun _ : S.Sf => (0 : _), x)))).1]
  rfl

theorem continuedEis_rootRep_compF {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) (v : FinPlace F) :
    P.compF v (continuedEis_rootRep P x) = 1 := by
  change P.compF v (Classical.choose
    (P.nS_components ((fun _ : S.Sf => (0 : _), x)))) = 1
  obtain ⟨_, hF, _⟩ := Classical.choose_spec
    (P.nS_components ((fun _ : S.Sf => (0 : _), x)))
  rw [hF v]
  by_cases hv : v ∈ S.Sf <;> simp [hv]

theorem continuedEis_rootRep_compC {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
    P.compC w (continuedEis_rootRep P x) = QuotientGroup.mk (upperM ℂ (x w)) := by
  exact (Classical.choose_spec
    (P.nS_components ((fun _ : S.Sf => (0 : _), x)))).2.2 w

noncomputable def continuedEis_archUnit (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (w : InfinitePlace F) : ℂˣ :=
  Units.mk0 ((y w : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')

theorem continuedEis_compU_atComplex (S : SData F CE condη)
    (v : S.Sf) (w : InfinitePlace F) (z : ℂˣ) :
    S.compU v (S.atComplex w z) = 1 := by
  apply Units.ext
  simp [SData.compU, SData.atComplex]

theorem continuedEis_compC_atComplex (S : SData F CE condη)
    (w w' : InfinitePlace F) (z : ℂˣ) :
    S.compC w (S.atComplex w' z) = if w = w' then z else 1 := by
  by_cases h : w = w'
  · subst w
    apply Units.ext
    simp [SData.compC, SData.atComplex]
  · apply Units.ext
    simp [SData.compC, SData.atComplex, h]

noncomputable def continuedEis_archLocalRep {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (w : InfinitePlace F) : P.RP :=
  Classical.choose (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))

noncomputable def continuedEis_archRep {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) : P.RP :=
  ((Finset.univ : Finset (InfinitePlace F)).toList.map
    (continuedEis_archLocalRep P y hy)).prod

theorem continuedEis_list_prod_eq_single {α M : Type} [Monoid M] [DecidableEq α]
    (l : List α) (hl : l.Nodup) (a : α) (ha : a ∈ l) (m : M) :
    (l.map fun b => if b = a then m else 1).prod = m := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.nodup_cons.mp hl with ⟨hb, hl⟩
    simp only [List.mem_cons] at ha
    by_cases h : b = a
    · subst b
      simp only [List.map_cons, List.prod_cons, if_pos rfl]
      have htail : (l.map fun b => if b = a then m else 1).prod = 1 := by
        apply List.prod_eq_one
        intro x hx
        rcases List.mem_map.mp hx with ⟨c, hc, rfl⟩
        have hne : c ≠ a := by
          intro hca
          subst c
          exact hb hc
        simp [hne]
      split_ifs <;> simp [htail]
    · have ha' : a ∈ l := by
        rcases ha with hEq | hmem
        · exact (h hEq.symm).elim
        · exact hmem
      simp only [List.map_cons, List.prod_cons, if_neg h, one_mul]
      exact ih hl ha'

theorem continuedEis_archRep_q {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) : P.q (continuedEis_archRep P y hy) = aInf P y := by
  classical
  unfold continuedEis_archRep aInf
  rw [dif_pos hy, map_list_prod]
  simp only [List.map_map]
  change (List.map (fun w => P.q (continuedEis_archLocalRep P y hy w))
      (Finset.univ : Finset (InfinitePlace F)).toList).prod =
    (List.map (fun w => P.tc.aS (S.atComplex w (continuedEis_archUnit y hy w)))
      (Finset.univ : Finset (InfinitePlace F)).toList).prod
  have hmap : List.map (fun w => P.q (continuedEis_archLocalRep P y hy w))
      (Finset.univ : Finset (InfinitePlace F)).toList =
    List.map (fun w => P.tc.aS (S.atComplex w (continuedEis_archUnit y hy w)))
      (Finset.univ : Finset (InfinitePlace F)).toList := by
    apply List.map_congr_left
    intro w hw
    exact (Classical.choose_spec
      (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))).1
  rw [hmap]

theorem continuedEis_archRep_compF {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (v : FinPlace F) :
    P.compF v (continuedEis_archRep P y hy) = 1 := by
  classical
  change P.compF v ((List.map (continuedEis_archLocalRep P y hy)
    (Finset.univ : Finset (InfinitePlace F)).toList).prod) = 1
  rw [map_list_prod]
  simp only [List.map_map]
  change (List.map (fun w => P.compF v (continuedEis_archLocalRep P y hy w))
    (Finset.univ : Finset (InfinitePlace F)).toList).prod = 1
  have hmap : List.map (fun w => P.compF v (continuedEis_archLocalRep P y hy w))
    (Finset.univ : Finset (InfinitePlace F)).toList =
    List.map (fun _ => (1 : (P.loc v).L))
    (Finset.univ : Finset (InfinitePlace F)).toList := by
    apply List.map_congr_left
    intro w hw
    obtain ⟨_, hF, _⟩ := Classical.choose_spec
      (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))
    change P.compF v (Classical.choose
      (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))) = _
    by_cases hv : v ∈ S.Sf
    · have hF' : P.compF v (Classical.choose
          (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))) =
        (P.loc v).a (S.compU ⟨v, hv⟩ (S.atComplex w (continuedEis_archUnit y hy w))) := by
        simpa [hv] using hF v
      rw [hF', continuedEis_compU_atComplex, (P.loc v).a_one]
    · simpa [hv] using hF v
  rw [hmap]
  simp

theorem continuedEis_archRep_compC {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (w : InfinitePlace F) :
    P.compC w (continuedEis_archRep P y hy) =
      QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y hy w)) := by
  classical
  change P.compC w ((List.map (continuedEis_archLocalRep P y hy)
    (Finset.univ : Finset (InfinitePlace F)).toList).prod) = _
  rw [map_list_prod]
  simp only [List.map_map]
  change (List.map (fun w' => P.compC w (continuedEis_archLocalRep P y hy w'))
    (Finset.univ : Finset (InfinitePlace F)).toList).prod = _
  have hmap : List.map (fun w' => P.compC w (continuedEis_archLocalRep P y hy w'))
    (Finset.univ : Finset (InfinitePlace F)).toList =
    List.map (fun w' => if w' = w then
      QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y hy w)) else 1)
    (Finset.univ : Finset (InfinitePlace F)).toList := by
    apply List.map_congr_left
    intro w' hw'
    obtain ⟨_, _, hC⟩ := Classical.choose_spec
      (P.aS_components (S.atComplex w' (continuedEis_archUnit y hy w')))
    change P.compC w (Classical.choose
      (P.aS_components (S.atComplex w' (continuedEis_archUnit y hy w')))) = _
    rw [hC]
    have hunit : S.compC w (S.atComplex w' (continuedEis_archUnit y hy w')) =
        if w' = w then continuedEis_archUnit y hy w else 1 := by
      rw [continuedEis_compC_atComplex]
      by_cases h : w' = w
      · subst w'
        simp
      · have h' : w ≠ w' := fun he => h he.symm
        simp [h, h']
    rw [hunit]
    have hdiag : diagM ℂ (1 : ℂˣ) = (1 : GL (Fin 2) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagM]
    by_cases h : w' = w
    · subst w'
      simp [hdiag]
    · simp [h, hdiag]
  rw [hmap]
  exact continuedEis_list_prod_eq_single
    (Finset.univ : Finset (InfinitePlace F)).toList
    (Finset.nodup_toList (Finset.univ : Finset (InfinitePlace F)))
    w (Finset.mem_toList.mpr (Finset.mem_univ w))
    (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y hy w)))

theorem continuedEis_mixed_commute {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) {g h : P.tc.G}
    (hg : ∃ x : P.RP, P.q x = g ∧ ∀ w, P.compC w x = 1)
    (hh : ∃ y : P.RP, P.q y = h ∧ ∀ v, P.compF v y = 1) : g * h = h * g := by
  obtain ⟨x, hqx, hxC⟩ := hg
  obtain ⟨y, hqy, hyF⟩ := hh
  have hxy : x * y = y * x := by
    apply P.comp_ext
    · intro v
      simp [hyF v]
    · intro w
      simp [hxC w]
  calc
    g * h = P.q x * P.q y := by rw [hqx, hqy]
    _ = P.q (x * y) := by simp
    _ = P.q (y * x) := by rw [hxy]
    _ = h * g := by rw [← hqy, ← hqx]; simp

theorem continuedEis_assoc_arch_product {G : Type*} [Group G]
    (a b c d e f g : G) :
    a⁻¹ * b * c * d * e * f * g = a⁻¹ * b * c * (d * e) * f * g := by
  group

theorem continuedEis_upperHom_matrix (z : ℂ) :
    ((ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
      (@Multiplicative.ofAdd ℂ z) : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, z; 0, 1] := rfl

theorem continuedEis_upperHom_pgl (z : ℂ) :
    Matrix.SpecialLinearGroup.toPGL
      (ArtinPrimitiveRoots.A1.Spec.upperHom ℂ (@Multiplicative.ofAdd ℂ z)) =
      QuotientGroup.mk (upperM ℂ z) := by
  have hGL : Matrix.SpecialLinearGroup.toGL
      (ArtinPrimitiveRoots.A1.Spec.upperHom ℂ (@Multiplicative.ofAdd ℂ z)) = upperM ℂ z := by
    have hSLmatrix := continuedEis_upperHom_matrix z
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    calc
      ((Matrix.SpecialLinearGroup.toGL
          (ArtinPrimitiveRoots.A1.Spec.upperHom ℂ (@Multiplicative.ofAdd ℂ z)) :
            GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j =
          ((ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
            (@Multiplicative.ofAdd ℂ z) : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) i j := by
        simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      _ = (!![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) i j :=
        congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A i j) hSLmatrix
      _ = ((upperM ℂ z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j := by
        simp [upperM]
  change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  rw [hGL]

end ArtinPrimitiveRoots.A1.Theta
