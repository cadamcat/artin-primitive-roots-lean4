import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_representatives

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open NumberField IsDedekindDomain
open scoped Classical ContDiff MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem continuedEis_componentTheta_contDiffOn
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

private theorem continuedEis_matrixMul_contDiff {E : Type*}
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

private noncomputable def continuedEis_slLiftPGL (g : PGL2 ℂ) : SL(2, ℂ) := by
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

private theorem continuedEis_slLiftPGL_toPGL (g : PGL2 ℂ) :
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

private theorem continuedEis_slFixBase_unitary (F : Type) [Field F] [NumberField F]
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

private theorem continuedEis_ptMat_smul_base (x : ℂ) (y : ℝ) (hy : 0 < y) :
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

private theorem continuedEis_ptMat_pgl (x : ℂ) (y : ℝ) (hy : 0 < y) :
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

private def continuedEis_baseDen (g : SL(2, ℂ)) : ℝ :=
  Complex.normSq (g 1 0) + Complex.normSq (g 1 1)

private def continuedEis_baseNum (g : SL(2, ℂ)) : ℂ :=
  g 0 0 * star (g 1 0) + g 0 1 * star (g 1 1)

private def continuedEis_baseCoord (g : SL(2, ℂ)) : ℂ × ℝ :=
  (continuedEis_baseNum g / (continuedEis_baseDen g : ℂ),
    (continuedEis_baseDen g)⁻¹)

private theorem continuedEis_baseDen_pos (g : SL(2, ℂ)) :
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

private theorem continuedEis_coords_base_action (g : SL(2, ℂ)) :
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

private theorem continuedEis_baseCoord_contDiff {E : Type*}
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

private noncomputable def continuedEis_conjugateRoot
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

private noncomputable def continuedEis_rootRep {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) : P.RP :=
  Classical.choose (P.nS_components ((fun _ : S.Sf => (0 : _), x)))

private theorem continuedEis_rootRep_q {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) :
    P.q (continuedEis_rootRep P x) = nInf P x := by
  change P.q (Classical.choose (P.nS_components ((fun _ : S.Sf => (0 : _), x)))) = _
  rw [(Classical.choose_spec (P.nS_components ((fun _ : S.Sf => (0 : _), x)))).1]
  rfl

private theorem continuedEis_rootRep_compF {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) (v : FinPlace F) :
    P.compF v (continuedEis_rootRep P x) = 1 := by
  change P.compF v (Classical.choose
    (P.nS_components ((fun _ : S.Sf => (0 : _), x)))) = 1
  obtain ⟨_, hF, _⟩ := Classical.choose_spec
    (P.nS_components ((fun _ : S.Sf => (0 : _), x)))
  rw [hF v]
  by_cases hv : v ∈ S.Sf <;> simp [hv]

private theorem continuedEis_rootRep_compC {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
    P.compC w (continuedEis_rootRep P x) = QuotientGroup.mk (upperM ℂ (x w)) := by
  exact (Classical.choose_spec
    (P.nS_components ((fun _ : S.Sf => (0 : _), x)))).2.2 w

private noncomputable def continuedEis_archUnit (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (w : InfinitePlace F) : ℂˣ :=
  Units.mk0 ((y w : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')

private theorem continuedEis_compU_atComplex (S : SData F CE condη)
    (v : S.Sf) (w : InfinitePlace F) (z : ℂˣ) :
    S.compU v (S.atComplex w z) = 1 := by
  apply Units.ext
  simp [SData.compU, SData.atComplex]

private theorem continuedEis_compC_atComplex (S : SData F CE condη)
    (w w' : InfinitePlace F) (z : ℂˣ) :
    S.compC w (S.atComplex w' z) = if w = w' then z else 1 := by
  by_cases h : w = w'
  · subst w
    apply Units.ext
    simp [SData.compC, SData.atComplex]
  · apply Units.ext
    simp [SData.compC, SData.atComplex, h]

private noncomputable def continuedEis_archLocalRep {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (w : InfinitePlace F) : P.RP :=
  Classical.choose (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))

private noncomputable def continuedEis_archRep {D : FieldData F} {CE : ℕ}
    {condη : Ideal (𝓞 F)} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) : P.RP :=
  ((Finset.univ : Finset (InfinitePlace F)).toList.map
    (continuedEis_archLocalRep P y hy)).prod

private theorem continuedEis_list_prod_eq_single {α M : Type} [Monoid M] [DecidableEq α]
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

private theorem continuedEis_archRep_q {D : FieldData F} {CE : ℕ}
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

private theorem continuedEis_archRep_compF {D : FieldData F} {CE : ℕ}
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

private theorem continuedEis_archRep_compC {D : FieldData F} {CE : ℕ}
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

private theorem continuedEis_mixed_commute {D : FieldData F} {CE : ℕ}
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

private theorem continuedEis_assoc_arch_product {G : Type*} [Group G]
    (a b c d e f g : G) :
    a⁻¹ * b * c * d * e * f * g = a⁻¹ * b * c * (d * e) * f * g := by
  group

private theorem continuedEis_upperHom_matrix (z : ℂ) :
    ((ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
      (@Multiplicative.ofAdd ℂ z) : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, z; 0, 1] := rfl

private theorem continuedEis_upperHom_pgl (z : ℂ) :
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

private theorem continuedEis_theta_jointRoots_chart
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) :
    ∀ g : P.tc.G, ∃ j : C.J,
      ∃ p : ((InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) →
          ArtinPrimitiveRoots.A1.Spec.Coord F,
        ContDiff ℝ ∞ p ∧
        (∀ q, p q ∈ ArtinPrimitiveRoots.A1.Spec.posSet F) ∧
        ∀ q, R.theta (nInf P q.1 * g * nInf P q.2) =
          C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) := by
  classical
  intro g
  obtain ⟨j, γ, x0, y0, kinf, k, hy0, hkinf, hk, hg⟩ :=
    continuedEis_component_representatives C g
  obtain ⟨rKin, hqKin, hFKin, hCKin⟩ := hkinf
  let kSL (w : InfinitePlace F) : SL(2, ℂ) :=
    continuedEis_slLiftPGL (P.compC w rKin)
  have hkSL (w : InfinitePlace F) :
      Matrix.SpecialLinearGroup.toPGL (kSL w) = P.compC w rKin :=
    continuedEis_slLiftPGL_toPGL (P.compC w rKin)
  let d (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ))
      (w : InfinitePlace F) : SL(2, ℂ) :=
    continuedEis_conjugateRoot (Matrix.GeneralLinearGroup.map w.embedding γ) (q.1 w)
  let M (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ))
      (w : InfinitePlace F) : SL(2, ℂ) :=
    d q w * ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) *
      kSL w * ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
        (@Multiplicative.ofAdd ℂ (q.2 w))
  let base : ArtinPrimitiveRoots.A1.Spec.X F := fun _ =>
    ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)
  let orbit (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      ArtinPrimitiveRoots.A1.Spec.X F :=
    ArtinPrimitiveRoots.A1.Spec.actAtPlaces F (M q) base
  let p (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      ArtinPrimitiveRoots.A1.Spec.Coord F := ArtinPrimitiveRoots.A1.Spec.coordsX F (orbit q)
  have hMentry : ∀ w i j, ContDiff ℝ ∞ (fun q :
      (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => M q w i j) := by
    intro w i j
    let gGL : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map w.embedding γ
    let nGL (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : GL (Fin 2) ℂ :=
      upperM ℂ (q.1 w)
    let gM : Matrix (Fin 2) (Fin 2) ℂ := (gGL : Matrix (Fin 2) (Fin 2) ℂ)
    let gInvM : Matrix (Fin 2) (Fin 2) ℂ := ((gGL⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
    let nM (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ := (nGL q : Matrix (Fin 2) (Fin 2) ℂ)
    have hgM : ∀ i j, ContDiff ℝ ∞ (fun q :
        (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => gM i j) := by
      intro i j
      exact contDiff_const
    have hgiM : ∀ i j, ContDiff ℝ ∞ (fun q :
        (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => gInvM i j) := by
      intro i j
      exact contDiff_const
    have hnM : ∀ i j, ContDiff ℝ ∞ (fun q :
        (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => nM q i j) := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [nM, nGL, upperM, Matrix.GeneralLinearGroup.mkOfDetNeZero] <;> fun_prop
    let d1M (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) := gInvM * nM q
    have hD1 := continuedEis_matrixMul_contDiff (fun _ => gInvM) nM hgiM hnM
    have hD2 := continuedEis_matrixMul_contDiff d1M (fun _ => gM) hD1 hgM
    have hD : ∀ i j, ContDiff ℝ ∞ (fun q => ((d q w : SL(2, ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) i j) := by
      intro i j
      change ContDiff ℝ ∞ (fun q => ((gInvM * nM q * gM) i j))
      simpa [d1M, Matrix.mul_assoc] using hD2 i j
    let ptM : Matrix (Fin 2) (Fin 2) ℂ :=
      (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) : Matrix (Fin 2) (Fin 2) ℂ)
    let kM : Matrix (Fin 2) (Fin 2) ℂ := (kSL w : Matrix (Fin 2) (Fin 2) ℂ)
    let uM (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ := !![1, q.2 w; 0, 1]
    have hptM : ∀ i j, ContDiff ℝ ∞ (fun _ :
        (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => ptM i j) := by
      intro i j
      exact contDiff_const
    have hkM : ∀ i j, ContDiff ℝ ∞ (fun _ :
        (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => kM i j) := by
      intro i j
      exact contDiff_const
    have huM : ∀ i j, ContDiff ℝ ∞ (fun q :
        (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => uM q i j) := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [uM] <;> fun_prop
    have h1 := continuedEis_matrixMul_contDiff (fun q =>
      ((d q w : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) (fun _ => ptM) hD hptM
    have h2 := continuedEis_matrixMul_contDiff (fun q =>
      ((d q w : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * ptM) (fun _ => kM) h1 hkM
    have h3 := continuedEis_matrixMul_contDiff (fun q =>
      ((d q w : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * ptM * kM) uM h2 huM
    let fM (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : ℂ :=
      (((d q w * ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) *
        kSL w * ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
          (@Multiplicative.ofAdd ℂ (q.2 w)) : SL(2, ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) i j)
    change ContDiff ℝ ∞ fM
    have hU (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
        ((ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
          (@Multiplicative.ofAdd ℂ (q.2 w)) : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) =
          uM q := by
      dsimp [uM]
      exact continuedEis_upperHom_matrix (q.2 w)
    have hEq : fM = fun q =>
        ((((d q w : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) * ptM * kM * uM q) i j) := by
      funext q
      dsimp [fM, ptM, kM]
      rw [hU q]
    rw [hEq]
    exact h3 i j
  have hpEq : p = fun q w => continuedEis_baseCoord (M q w) := by
    funext q w
    change (ArtinPrimitiveRoots.A1.Spec.horiz
        (M q w • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)),
      ArtinPrimitiveRoots.A1.Spec.height
        (M q w • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ))) = _
    exact congrFun (continuedEis_coords_base_action (M q w)) w
  have hpSmooth : ContDiff ℝ ∞ p := by
    rw [hpEq]
    rw [contDiff_pi]
    intro w
    exact continuedEis_baseCoord_contDiff (fun q => M q w)
      (fun i j => hMentry w i j)
  have hpPos (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      p q ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro w
    rw [hpEq]
    exact inv_pos.mpr (continuedEis_baseDen_pos (M q w))
  have hpHeight (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      ∀ w, 0 < (p q w).2 := by
    simpa [ArtinPrimitiveRoots.A1.Spec.posSet] using hpPos q
  have hptX (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      ArtinPrimitiveRoots.A1.Spec.ptX F (p q) = orbit q := by
    funext w
    exact ArtinPrimitiveRoots.A1.Spec.pt_horiz_height (orbit q w)
  let b (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.tc.G :=
    nInf P (fun w => (p q w).1) * aInf P (fun w => (p q w).2)
  let rB (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.RP :=
    continuedEis_rootRep P (fun w => (p q w).1) *
      continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)
  have hqB (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      P.q (rB q) = b q := by
    change P.q (continuedEis_rootRep P (fun w => (p q w).1) *
        continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)) = _
    rw [map_mul, continuedEis_rootRep_q, continuedEis_archRep_q]
  have hFB (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) (v : FinPlace F) :
      P.compF v (rB q) = 1 := by
    change P.compF v (continuedEis_rootRep P (fun w => (p q w).1) *
        continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)) = _
    rw [map_mul, continuedEis_rootRep_compF, continuedEis_archRep_compF]
    simp
  have hCB (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ))
      (w : InfinitePlace F) :
      P.compC w (rB q) = Matrix.SpecialLinearGroup.toPGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat (p q w).1 (p q w).2 (hpPos q w)) := by
    have hroot : P.compC w (continuedEis_rootRep P (fun w => (p q w).1)) =
        QuotientGroup.mk (upperM ℂ (p q w).1) :=
      continuedEis_rootRep_compC P (fun w => (p q w).1) w
    have harch : P.compC w (continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)) =
        QuotientGroup.mk (diagM ℂ (continuedEis_archUnit (fun w => (p q w).2)
          (hpHeight q) w)) :=
      continuedEis_archRep_compC P (fun w => (p q w).2) (hpHeight q) w
    have hcan : (QuotientGroup.mk (upperM ℂ (p q w).1) : PGL2 ℂ) *
        (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit (fun w => (p q w).2)
          (hpHeight q) w)) : PGL2 ℂ) =
        Matrix.SpecialLinearGroup.toPGL
          (ArtinPrimitiveRoots.A1.Spec.ptMat (p q w).1 (p q w).2 (hpPos q w)) := by
      have hmul : (QuotientGroup.mk (upperM ℂ (p q w).1) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit (fun w => (p q w).2)
            (hpHeight q) w)) : PGL2 ℂ) =
          (QuotientGroup.mk (upperM ℂ (p q w).1 *
            diagM ℂ (continuedEis_archUnit (fun w => (p q w).2) (hpHeight q) w)) : PGL2 ℂ) := by
        change Matrix.ProjGenLinGroup.mk (upperM ℂ (p q w).1) *
            Matrix.ProjGenLinGroup.mk (diagM ℂ (continuedEis_archUnit
              (fun w => (p q w).2) (hpHeight q) w)) = _
        exact ((Matrix.ProjGenLinGroup.mk).map_mul _ _).symm
      have hmat : (QuotientGroup.mk (upperM ℂ (p q w).1 *
          diagM ℂ (continuedEis_archUnit (fun w => (p q w).2) (hpHeight q) w)) : PGL2 ℂ) =
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.ptMat (p q w).1 (p q w).2 (hpPos q w)) := by
        change QuotientGroup.mk (upperM ℂ (p q w).1 *
            diagM ℂ (continuedEis_archUnit (fun w => (p q w).2) (hpHeight q) w)) =
          QuotientGroup.mk (ArtinPrimitiveRoots.A1.Spec.ptMat
            (p q w).1 (p q w).2 (hpPos q w) : GL (Fin 2) ℂ)
        simpa [continuedEis_archUnit] using
          (continuedEis_ptMat_pgl (p q w).1 (p q w).2 (hpPos q w)).symm
      exact hmul.trans hmat
    have hBmap : P.compC w (rB q) =
        P.compC w (continuedEis_rootRep P (fun w => (p q w).1)) *
          P.compC w (continuedEis_archRep P (fun w => (p q w).2) (hpHeight q)) := by
      exact (P.compC w).map_mul _ _
    rw [hroot, harch] at hBmap
    exact hBmap.trans hcan
  let rA (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.RP :=
    (P.ratRP γ)⁻¹ * continuedEis_rootRep P q.1 * P.ratRP γ *
      continuedEis_rootRep P x0 * continuedEis_archRep P y0 hy0 * rKin *
      continuedEis_rootRep P q.2
  have hqA (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      P.q (rA q) = (P.tc.rat γ)⁻¹ * nInf P q.1 * P.tc.rat γ *
        nInf P x0 * aInf P y0 * kinf * nInf P q.2 := by
    simp [rA, map_mul, map_inv, P.q_ratRP, continuedEis_rootRep_q,
      continuedEis_archRep_q, hqKin]
  have hFA (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) (v : FinPlace F) :
      P.compF v (rA q) = 1 := by
    simp [rA, map_mul, map_inv, P.compF_ratRP, continuedEis_rootRep_compF,
      continuedEis_archRep_compF, hFKin]
  have hCA (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ))
      (w : InfinitePlace F) :
      P.compC w (rA q) = Matrix.SpecialLinearGroup.toPGL (M q w) := by
    have hd : Matrix.SpecialLinearGroup.toPGL (d q w) =
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
          (QuotientGroup.mk (upperM ℂ (q.1 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) := by
      have hGL : Matrix.SpecialLinearGroup.toGL (d q w) =
          (Matrix.GeneralLinearGroup.map w.embedding γ)⁻¹ * upperM ℂ (q.1 w) *
            Matrix.GeneralLinearGroup.map w.embedding γ := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change (((continuedEis_conjugateRoot
          (Matrix.GeneralLinearGroup.map w.embedding γ) (q.1 w) : SL(2, ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) i j) =
          ((((Matrix.GeneralLinearGroup.map w.embedding γ)⁻¹ * upperM ℂ (q.1 w) *
            Matrix.GeneralLinearGroup.map w.embedding γ : GL (Fin 2) ℂ) :
              Matrix (Fin 2) (Fin 2) ℂ) i j)
        rfl
      change (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (d q w)) : PGL2 ℂ) = _
      rw [hGL]
      change Matrix.ProjGenLinGroup.mk
          ((Matrix.GeneralLinearGroup.map w.embedding γ)⁻¹ * upperM ℂ (q.1 w) *
            Matrix.GeneralLinearGroup.map w.embedding γ) = _
      simp only [Matrix.ProjGenLinGroup.mk.map_mul, map_inv]
    have hpt : Matrix.SpecialLinearGroup.toPGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)) =
        (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) := by
      have hptMat : Matrix.SpecialLinearGroup.toPGL
          (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)) =
          (QuotientGroup.mk (upperM ℂ (x0 w) *
            diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) := by
        change Matrix.ProjGenLinGroup.mk
            (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) : GL (Fin 2) ℂ) = _
        exact continuedEis_ptMat_pgl (x0 w) (y0 w) (hy0 w)
      have hptMul : (QuotientGroup.mk (upperM ℂ (x0 w) *
          diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) =
          (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
            (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) := by
        change Matrix.ProjGenLinGroup.mk
            (upperM ℂ (x0 w) * diagM ℂ (continuedEis_archUnit y0 hy0 w)) =
          Matrix.ProjGenLinGroup.mk (upperM ℂ (x0 w)) *
            Matrix.ProjGenLinGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w))
        exact (Matrix.ProjGenLinGroup.mk).map_mul _ _
      exact hptMat.trans hptMul
    have hAraw : P.compC w (rA q) =
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
          (QuotientGroup.mk (upperM ℂ (q.1 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) *
          (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) *
          P.compC w rKin * (QuotientGroup.mk (upperM ℂ (q.2 w)) : PGL2 ℂ) := by
      simp only [rA, map_mul, map_inv, P.compC_ratRP,
        continuedEis_rootRep_compC, continuedEis_archRep_compC]
    have hAmap :
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
          (QuotientGroup.mk (upperM ℂ (q.1 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) *
          (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) *
          P.compC w rKin * (QuotientGroup.mk (upperM ℂ (q.2 w)) : PGL2 ℂ) =
        Matrix.SpecialLinearGroup.toPGL (d q w) *
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)) *
          Matrix.SpecialLinearGroup.toPGL (kSL w) *
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
              (@Multiplicative.ofAdd ℂ (q.2 w))) := by
      have hDpart :
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
            (QuotientGroup.mk (upperM ℂ (q.1 w)) : PGL2 ℂ) *
            (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) =
          Matrix.SpecialLinearGroup.toPGL (d q w) := hd.symm
      have hPtpart : (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
          (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ) =
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)) := hpt.symm
      have hKinpart : P.compC w rKin = Matrix.SpecialLinearGroup.toPGL (kSL w) :=
        (hkSL w).symm
      have hNpart : (QuotientGroup.mk (upperM ℂ (q.2 w)) : PGL2 ℂ) =
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
              (@Multiplicative.ofAdd ℂ (q.2 w))) :=
        (continuedEis_upperHom_pgl (q.2 w)).symm
      calc
        _ = (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
              (QuotientGroup.mk (upperM ℂ (q.1 w)) : PGL2 ℂ) *
              (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) *
              ((QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
                (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) : PGL2 ℂ)) *
              P.compC w rKin * QuotientGroup.mk (upperM ℂ (q.2 w)) :=
          continuedEis_assoc_arch_product _ _ _ _ _ _ _
        _ = _ := by rw [hDpart, hPtpart, hKinpart, hNpart]
    have hMmap : Matrix.SpecialLinearGroup.toPGL (d q w) *
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)) *
          Matrix.SpecialLinearGroup.toPGL (kSL w) *
          Matrix.SpecialLinearGroup.toPGL
            (ArtinPrimitiveRoots.A1.Spec.upperHom ℂ
              (@Multiplicative.ofAdd ℂ (q.2 w))) =
        Matrix.SpecialLinearGroup.toPGL (M q w) := by
      simp [M, map_mul]
    exact hAraw.trans (hAmap.trans hMmap)
  let rRes (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.RP :=
    (rB q)⁻¹ * rA q
  let κ (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.tc.G := P.q (rRes q)
  have hκ (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : κ q ∈ infCompact P := by
    refine ⟨rRes q, rfl, ?_, ?_⟩
    · intro v
      simp [rRes, map_mul, map_inv, hFA q v, hFB q v]
    · intro w
      let s := (ArtinPrimitiveRoots.A1.Spec.ptMat (p q w).1 (p q w).2 (hpPos q w))⁻¹ * M q w
      have hfix : s • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
          ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) := by
        dsimp [s]
        rw [mul_smul]
        have hhor : (p q w).1 = ArtinPrimitiveRoots.A1.Spec.horiz
            (M q w • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) := rfl
        have hheight : (p q w).2 = ArtinPrimitiveRoots.A1.Spec.height
            (M q w • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) := rfl
        have horbit : M q w • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
            ArtinPrimitiveRoots.A1.Spec.pt (p q w).1 (p q w).2 := by
          rw [hhor, hheight]
          exact (ArtinPrimitiveRoots.A1.Spec.pt_horiz_height
            (M q w • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ))).symm
        rw [horbit, ← continuedEis_ptMat_smul_base (p q w).1 (p q w).2 (hpPos q w)] <;> simp
      refine ⟨(s : GL (Fin 2) ℂ), continuedEis_slFixBase_unitary F s hfix, ?_⟩
      have hCres : P.compC w (rRes q) =
          Matrix.SpecialLinearGroup.toPGL s := by
        calc
          P.compC w (rRes q) =
              (Matrix.SpecialLinearGroup.toPGL
                (ArtinPrimitiveRoots.A1.Spec.ptMat (p q w).1 (p q w).2 (hpPos q w)))⁻¹ *
                Matrix.SpecialLinearGroup.toPGL (M q w) := by
              rw [rRes, map_mul, map_inv, hCB q w, hCA q w]
          _ = Matrix.SpecialLinearGroup.toPGL s := by
              simp [s, map_mul, map_inv]
      change P.compC w (rRes q) = Matrix.SpecialLinearGroup.toPGL s
      exact hCres
  have hκcomm (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      κ q * j = j * κ q := by
    have hj := C.finite_components j j.property
    have hκF : ∃ x : P.RP, P.q x = κ q ∧ ∀ v, P.compF v x = 1 := by
      refine ⟨rRes q, ?_, ?_⟩
      · rfl
      · intro v
        simp [rRes, map_mul, map_inv, hFA q v, hFB q v]
    exact (continuedEis_mixed_commute P hj hκF).symm
  have hkRoot (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      k * nInf P q.2 = nInf P q.2 * k := by
    obtain ⟨rK, hqK, hKC, _⟩ := hk
    have hRoot : ∃ rU : P.RP, P.q rU = nInf P q.2 ∧ ∀ v, P.compF v rU = 1 :=
      ⟨continuedEis_rootRep P q.2, continuedEis_rootRep_q P q.2,
        continuedEis_rootRep_compF P q.2⟩
    exact continuedEis_mixed_commute P ⟨rK, hqK, hKC⟩ hRoot
  have hjKin : j * kinf = kinf * j := by
    have hj := C.finite_components j j.property
    exact continuedEis_mixed_commute P hj ⟨rKin, hqKin, hFKin⟩
  have hjRoot (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      j * nInf P q.2 = nInf P q.2 * j := by
    have hj := C.finite_components j j.property
    have hRoot : ∃ rU : P.RP, P.q rU = nInf P q.2 ∧ ∀ v, P.compF v rU = 1 :=
      ⟨continuedEis_rootRep P q.2, continuedEis_rootRep_q P q.2,
        continuedEis_rootRep_compF P q.2⟩
    exact continuedEis_mixed_commute P hj hRoot
  have hjTail (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      j * (kinf * nInf P q.2) = (kinf * nInf P q.2) * j := by
    calc
      j * (kinf * nInf P q.2) = (j * kinf) * nInf P q.2 := by group
      _ = (kinf * j) * nInf P q.2 := by rw [hjKin]
      _ = kinf * (j * nInf P q.2) := by group
      _ = kinf * (nInf P q.2 * j) := by rw [hjRoot q]
      _ = (kinf * nInf P q.2) * j := by group
  let δ (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) : P.tc.G :=
    (P.tc.rat γ)⁻¹ * nInf P q.1 * P.tc.rat γ
  have hconj (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      nInf P q.1 * P.tc.rat γ = P.tc.rat γ * δ q := by
    dsimp [δ]
    group
  have hqA' (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      P.q (rA q) = δ q * nInf P x0 * aInf P y0 * kinf * nInf P q.2 := by
    simpa [δ] using hqA q
  have hbκ (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      b q * κ q = P.q (rA q) := by
    calc
      b q * κ q = P.q (rB q) * P.q (rRes q) := by rw [hqB]
      _ = P.q (rB q * rRes q) := by simp
      _ = P.q (rA q) := by simp [rRes]
  have hOrbitGroup (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      nInf P q.1 * g * nInf P q.2 =
        P.tc.rat γ * ((b q * j) * κ q * k) := by
    have hMoveK :
        ((nInf P x0 * aInf P y0 * j) * kinf * k) * nInf P q.2 =
          ((nInf P x0 * aInf P y0 * j) * kinf * nInf P q.2) * k := by
      calc
        _ = (nInf P x0 * aInf P y0 * j) * kinf * (k * nInf P q.2) := by group
        _ = (nInf P x0 * aInf P y0 * j) * kinf * (nInf P q.2 * k) := by rw [hkRoot q]
        _ = _ := by group
    have hMoveJ :
        (nInf P x0 * aInf P y0 * j) * kinf * nInf P q.2 =
          (nInf P x0 * aInf P y0 * kinf * nInf P q.2) * j := by
      calc
        _ = (nInf P x0 * aInf P y0) * (j * (kinf * nInf P q.2)) := by group
        _ = (nInf P x0 * aInf P y0) * ((kinf * nInf P q.2) * j) := by rw [hjTail q]
        _ = _ := by group
    calc
      nInf P q.1 * g * nInf P q.2 =
          nInf P q.1 * (P.tc.rat γ * ((nInf P x0 * aInf P y0 * j) * kinf * k)) *
            nInf P q.2 := by rw [hg]; group
      _ =
          P.tc.rat γ * (δ q * (((nInf P x0 * aInf P y0 * j) * kinf * k) *
            nInf P q.2)) := by rw [← mul_assoc, hconj q]; group
      _ = P.tc.rat γ * (δ q *
          ((nInf P x0 * aInf P y0 * j) * kinf * nInf P q.2) * k) := by
        rw [hMoveK]
        group
      _ = P.tc.rat γ * ((P.q (rA q) * j) * k) := by
        rw [hMoveJ]
        calc
          P.tc.rat γ * (δ q * (nInf P x0 * aInf P y0 * kinf * nInf P q.2 * j) * k) =
              P.tc.rat γ * ((δ q * nInf P x0 * aInf P y0 * kinf * nInf P q.2 * j) * k) := by
            congr 1
            group
          _ = P.tc.rat γ * ((P.q (rA q) * j) * k) := by rw [← hqA' q]
      _ = P.tc.rat γ * ((b q * κ q * j) * k) := by
        rw [← hbκ q]
      _ = P.tc.rat γ * ((b q * j) * κ q * k) := by
        have horder : b q * κ q * j = b q * j * κ q := by
          calc
            b q * κ q * j = b q * (κ q * j) := by group
            _ = b q * (j * κ q) := by rw [hκcomm q]
            _ = b q * j * κ q := by group
        rw [horder]
  have hthetaEq (q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)) :
      R.theta (nInf P q.1 * g * nInf P q.2) =
        C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) := by
    rw [hOrbitGroup q]
    calc
      R.theta (P.tc.rat γ * ((b q * j) * κ q * k)) =
          R.theta (((b q * j) * κ q) * k) := R.theta_aut γ _
      _ = R.theta ((b q * j) * κ q) := R.theta_level ((b q * j) * κ q) k hk
      _ = R.theta (b q * j) := R.theta_compact (b q * j) (κ q) (hκ q)
      _ = C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) := by
        have hcoords : ArtinPrimitiveRoots.A1.Spec.coordsX F
            (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) = p q := by
          funext w
          simp [ArtinPrimitiveRoots.A1.Spec.coordsX,
            ArtinPrimitiveRoots.A1.Spec.ptX, ArtinPrimitiveRoots.A1.Spec.horiz_pt,
            ArtinPrimitiveRoots.A1.Spec.height_pt, hpPos q w]
        have hfst : (fun w => ArtinPrimitiveRoots.A1.Spec.horiz
            (ArtinPrimitiveRoots.A1.Spec.ptX F (p q) w)) = fun w => (p q w).1 := by
          funext w
          exact congrArg Prod.fst (congrFun hcoords w)
        have hsnd : (fun w => ArtinPrimitiveRoots.A1.Spec.height
            (ArtinPrimitiveRoots.A1.Spec.ptX F (p q) w)) = fun w => (p q w).2 := by
          funext w
          exact congrArg Prod.snd (congrFun hcoords w)
        have hclassical : classicalOf P R.theta j
            (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) = R.theta (b q * j) := by
          dsimp [classicalOf, b]
          rw [hfst, hsnd]
        calc
          R.theta (b q * j) = classicalOf P R.theta j
              (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) := hclassical.symm
          _ = C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p q)) :=
            congrFun (R.theta_component j) _
  exact ⟨j, p, hpSmooth, hpPos, hthetaEq⟩

theorem continuedEis_theta_jointRoots
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) : JointRootSmooth P R.theta := by
  classical
  intro g
  obtain ⟨j, p, hpSmooth, hpPos, hthetaEq⟩ :=
    continuedEis_theta_jointRoots_chart R g
  have hComp : ContDiffOn ℝ ∞
      (fun z : ArtinPrimitiveRoots.A1.Spec.Coord F =>
        C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F z))
      (ArtinPrimitiveRoots.A1.Spec.posSet F) :=
    continuedEis_componentTheta_contDiffOn C j
  have hCompose := hComp.comp_contDiff hpSmooth hpPos
  have hEq : (fun q : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) =>
      R.theta (nInf P q.1 * g * nInf P q.2)) =
      (fun q => C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p q))) := by
    funext q
    exact hthetaEq q
  rw [hEq]
  exact hCompose

end ArtinPrimitiveRoots.A1.Theta
