import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_coord_smooth
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.radialKernel_support_thickening

set_option autoImplicit false
open NumberField
open scoped ContDiff Pointwise

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem iteratedFDeriv_coord_section_eq
    (f : Coord F × Coord F → ℂ)
    (hf : ContDiffOn ℝ ∞ f {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F})
    (hSopen : IsOpen {pq : Coord F × Coord F | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F})
    (hposOpen : IsOpen (posSet F))
    (p q : Coord F) (hp : p ∈ posSet F) (hq : q ∈ posSet F) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => f (x, q)) p =
      (iteratedFDeriv ℝ n f (p, q)).compContinuousLinearMap
        (fun _ : Fin n => ContinuousLinearMap.inl ℝ (Coord F) (Coord F)) := by
  classical
  let S : Set (Coord F × Coord F) := {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F}
  let L : Coord F →L[ℝ] Coord F × Coord F :=
    ContinuousLinearMap.inl ℝ (Coord F) (Coord F)
  let R : Coord F →L[ℝ] Coord F × Coord F :=
    ContinuousLinearMap.inr ℝ (Coord F) (Coord F)
  let T : Set (Coord F × Coord F) := (fun x => x + R q) ⁻¹' S
  have hTopen : IsOpen T := by
    apply hSopen.preimage
    fun_prop
  have hpre : L ⁻¹' T = posSet F := by
    ext x
    simp [T, S, L, R, hq]
  have hpreUnique : UniqueDiffOn ℝ (L ⁻¹' T) := by
    rw [hpre]
    exact hposOpen.uniqueDiffOn
  have htranslate : R q +ᵥ T = S := by
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp [T, S, R, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  have hshift : ContDiffOn ℝ ∞ (fun x => f (x + R q)) T := by
    have htrans : ContDiff ℝ ∞ (fun x : Coord F × Coord F => x + R q) := by fun_prop
    have hmaps : Set.MapsTo (fun x : Coord F × Coord F => x + R q) T S := by
      intro x hx
      exact hx
    exact hf.comp htrans.contDiffOn hmaps
  have hxT : L p ∈ T := by
    have hp' : p ∈ L ⁻¹' T := by rw [hpre]; exact hp
    exact Set.mem_preimage.mp hp'
  have hchain := L.iteratedFDerivWithin_comp_right hshift hTopen.uniqueDiffOn
    hpreUnique hxT (i := n) (by simp)
  have hshiftEq : iteratedFDerivWithin ℝ n (fun x => f (x + R q)) T (L p) =
      iteratedFDerivWithin ℝ n f (R q +ᵥ T) (L p + R q) := by
    exact iteratedFDerivWithin_comp_add_right n (R q) (L p)
  have hpoint : L p + R q = (p, q) := by
    simp [L, R]
  have hsecEq : (fun x : Coord F => f (L x + R q)) = (fun x => f (x, q)) := by
    funext x
    simp [L, R]
  have hsecComp : (fun x : Coord F × Coord F => f (x + R q)) ∘ L =
      (fun x => f (x, q)) := by
    funext x
    exact congrFun hsecEq x
  rw [hsecComp, hpre, hshiftEq, htranslate, hpoint] at hchain
  have hsec : ContDiffOn ℝ ∞ (fun x : Coord F => f (x, q)) (posSet F) := by
    have hmap : ContDiff ℝ ∞ (fun x : Coord F => (x, q)) := by fun_prop
    have hmaps : Set.MapsTo (fun x : Coord F => (x, q)) (posSet F) S := by
      intro x hx
      exact ⟨hx, hq⟩
    exact hf.comp hmap.contDiffOn hmaps
  have hsecAt : ContDiffAt ℝ ∞ (fun x : Coord F => f (x, q)) p :=
    hsec.contDiffAt (hposOpen.mem_nhds hp)
  have hjointAt : ContDiffAt ℝ ∞ f (p, q) :=
    hf.contDiffAt (hSopen.mem_nhds ⟨hp, hq⟩)
  have hsecWithin := iteratedFDerivWithin_eq_iteratedFDeriv (n := n)
    hposOpen.uniqueDiffOn (hsecAt.of_le (by simp)) hp
  have hjointWithin := iteratedFDerivWithin_eq_iteratedFDeriv (n := n)
    hSopen.uniqueDiffOn (hjointAt.of_le (by simp)) (show (p, q) ∈ S from ⟨hp, hq⟩)
  calc
    iteratedFDeriv ℝ n (fun x => f (x, q)) p =
        iteratedFDerivWithin ℝ n (fun x => f (x, q)) (posSet F) p := hsecWithin.symm
    _ = (iteratedFDerivWithin ℝ n f S (p, q)).compContinuousLinearMap
          (fun _ : Fin n => L) := hchain
    _ = (iteratedFDeriv ℝ n f (p, q)).compContinuousLinearMap
          (fun _ : Fin n => L) := by rw [hjointWithin]

/-- A common positive coordinate neighborhood, compact integration set, and bounds for every
kernel derivative. Nonnegativity and nonvanishing of the kernel are not required.
Guide: `sol-thin-spec/PROOFS.md:402–405`. Uses `radialKernel_coord_smooth`,
`radialKernel_support_thickening` and frozen `G1_h3_basics`; supplies the control hypothesis
of `param_deriv_integral_formula`, hence S1 and S3. -/
theorem radialKernel_compact_control (k₀ : ℝ → ℝ)
    (hkSmooth : ContDiff ℝ ∞ k₀)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ (U : Set (Coord F)) (W : Set (X F)),
      IsOpen U ∧ K ⊆ U ∧ U ⊆ posSet F ∧ IsCompact W ∧
        SmoothingKernelControl F k₀ U W := by
  classical
  by_cases hKempty : K = ∅
  · subst K
    refine ⟨∅, ∅, isOpen_empty, by simp, by simp, isCompact_empty, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro w
      exact contDiffOn_empty
    · intro n p hp
      exact hp.elim
    · intro n p hp
      exact hp.elim
    · intro n
      exact ⟨0, le_rfl, fun p hp w => hp.elim⟩
  · have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
    rcases G1_h3_basics (F := F) with
      ⟨hheight, hhoriz, _, _, _, _, _, hptX, _, _, _, hchart⟩
    obtain ⟨e, _, heCoords⟩ := hchart
    have hposOpen : IsOpen (posSet F) := by
      rw [posSet, Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro v
      have hc : Continuous (fun p : Coord F => (p v).2) := by fun_prop
      exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hcoordsPos (z : X F) : coordsX F z ∈ posSet F := by
      intro v
      change 0 < height (z v)
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z v)
    have hcoordsCont : Continuous (coordsX F) := by
      have heq : (fun z : X F => (e.symm z).1) = coordsX F := by
        funext z
        exact heCoords z
      rw [← heq]
      exact continuous_subtype_val.comp e.symm.continuous
    have hsecondCountableX : SecondCountableTopology (X F) := e.symm.secondCountableTopology
    letI : SecondCountableTopology (X F) := hsecondCountableX
    have hsecondCountableH3 : SecondCountableTopology H3 := by
      let w₀ : InfinitePlace F := Classical.choice inferInstance
      let c : H3 → X F := fun z _ => z
      let eval : X F → H3 := fun z => z w₀
      have hc : Continuous c := by
        change Continuous (fun z : H3 => fun _ : InfinitePlace F => z)
        exact continuous_pi fun _ => continuous_id
      have heval : Continuous eval := continuous_apply w₀
      have hleft : Function.LeftInverse eval c := by
        intro z
        simp [eval, c]
      exact hleft.isEmbedding heval hc |>.secondCountableTopology
    letI : SecondCountableTopology H3 := hsecondCountableH3
    letI : BorelSpace H3 := ⟨rfl⟩
    letI : Countable (InfinitePlace F) := Finite.to_countable
    letI : BorelSpace (X F) := by
      change BorelSpace (∀ v : InfinitePlace F, H3)
      exact Pi.borelSpace
    letI : OpensMeasurableSpace (X F) := BorelSpace.opensMeasurable
    let S : Set (Coord F × Coord F) := {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F}
    let joint : Coord F × Coord F → ℂ := fun pq =>
      radialKernel F k₀ (ptX F pq.1) (ptX F pq.2)
    have hSopen : IsOpen S := by
      change IsOpen (posSet F ×ˢ posSet F)
      exact hposOpen.prod hposOpen
    have hjoint : ContDiffOn ℝ ∞ joint S := by
      simpa [joint, S] using radialKernel_coord_smooth (F := F) k₀ hkSmooth
    have hsection (q : Coord F) (hq : q ∈ posSet F) :
        ContDiffOn ℝ ∞ (fun p : Coord F => joint (p, q)) (posSet F) := by
      have hmap : ContDiff ℝ ∞ (fun p : Coord F => (p, q)) := by fun_prop
      have hmaps : Set.MapsTo (fun p : Coord F => (p, q)) (posSet F) S := by
        intro p hp
        exact ⟨hp, hq⟩
      exact hjoint.comp hmap.contDiffOn hmaps
    obtain ⟨U, W, hUopen, hKU, hUclosureCompact, hUclosurePos, hWcompact,
      hkernelSupport⟩ := radialKernel_support_thickening k₀ hkSupport K hK hKpos
    have hUpos : U ⊆ posSet F := fun p hp => hUclosurePos (subset_closure hp)
    have hsectionSmooth (w : X F) :
        ContDiffOn ℝ ∞ (fun p => radialKernel F k₀ (ptX F p) w) U := by
      have h := (hsection (coordsX F w) (hcoordsPos w)).mono hUpos
      apply h.congr
      intro p hp
      simp [joint, hptX w]
    let Q : Set (Coord F) := coordsX F '' W
    have hQcompact : IsCompact Q := by
      exact hWcompact.image hcoordsCont
    let P : Set (Coord F × Coord F) := closure U ×ˢ Q
    have hPcompact : IsCompact P := hUclosureCompact.prod hQcompact
    have hPsubset : P ⊆ S := by
      rintro ⟨p, q⟩ ⟨hp, hq⟩
      rcases hq with ⟨w, hw, rfl⟩
      exact ⟨hUclosurePos hp, hcoordsPos w⟩
    have hderivJointContinuous (n : ℕ) :
        ContinuousOn (fun pq => iteratedFDeriv ℝ n joint pq) S :=
      ContinuousOn.continuousOn_iteratedFDeriv hjoint hSopen (by simp)
    have hsectionDerivContinuous (n : ℕ) (p : Coord F) (hp : p ∈ posSet F) :
        ContinuousOn
          (fun q => (iteratedFDeriv ℝ n joint (p, q)).compContinuousLinearMap
            (fun _ : Fin n => ContinuousLinearMap.inl ℝ (Coord F) (Coord F)))
          (posSet F) := by
      have hmaps : Set.MapsTo (fun q : Coord F => (p, q)) (posSet F) S := by
        intro q hq
        exact ⟨hp, hq⟩
      have hpair : ContinuousOn (fun q : Coord F => (p, q)) (posSet F) := by fun_prop
      have hD := (hderivJointContinuous n).comp hpair hmaps
      have hcompContinuous : Continuous
          (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F × Coord F) ℂ =>
            D.compContinuousLinearMap
              (fun _ : Fin n => ContinuousLinearMap.inl ℝ (Coord F) (Coord F))) := by
        exact (isBoundedLinearMap_continuousMultilinearMap_comp_linear
          (𝕜 := ℝ) (ι := Fin n) (F := ℂ)
          (ContinuousLinearMap.inl ℝ (Coord F) (Coord F))).continuous
      exact hcompContinuous.comp_continuousOn hD
    have hsectionDerivative (n : ℕ) (p : Coord F) (hp : p ∈ U) (w : X F) :
        iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p =
          (iteratedFDeriv ℝ n joint (p, coordsX F w)).compContinuousLinearMap
            (fun _ : Fin n => ContinuousLinearMap.inl ℝ (Coord F) (Coord F)) := by
      have hEq : (fun q => radialKernel F k₀ (ptX F q) w) =
          (fun q => joint (q, coordsX F w)) := by
        funext q
        simp [joint, hptX w]
      rw [hEq]
      exact iteratedFDeriv_coord_section_eq joint hjoint hSopen hposOpen p
        (coordsX F w) (hUpos hp) (hcoordsPos w) n
    have hderivZero (n : ℕ) (p : Coord F) (hp : p ∈ U) (w : X F) (hw : w ∉ W) :
        iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p = 0 := by
      have hEqOn : Set.EqOn (fun q => radialKernel F k₀ (ptX F q) w)
          (fun _ : Coord F => (0 : ℂ)) U := by
        intro q hq
        exact hkernelSupport q (subset_closure hq) w hw
      have hwithinEq := iteratedFDerivWithin_congr (𝕜 := ℝ) hEqOn hp n
      have hAt : ContDiffAt ℝ ∞
          (fun q => radialKernel F k₀ (ptX F q) w) p :=
        hsectionSmooth w |>.contDiffAt (hUopen.mem_nhds hp)
      have hwithinAt := iteratedFDerivWithin_eq_iteratedFDeriv (n := n)
        hUopen.uniqueDiffOn (hAt.of_le (by simp)) hp
      calc
        iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p =
            iteratedFDerivWithin ℝ n (fun q => radialKernel F k₀ (ptX F q) w) U p :=
              hwithinAt.symm
        _ = iteratedFDerivWithin ℝ n (fun _ : Coord F => (0 : ℂ)) U p := hwithinEq
        _ = 0 := by simp
    refine ⟨U, W, hUopen, hKU, hUpos, hWcompact, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hsectionSmooth
    · intro n p hp
      have hcoordsMap : Set.MapsTo (coordsX F) Set.univ (posSet F) := by
        intro w hw
        exact hcoordsPos w
      have hpairMap : Set.MapsTo (fun w : X F => (p, coordsX F w)) Set.univ S := by
        intro w hw
        exact ⟨hUpos hp, hcoordsPos w⟩
      have hpairContinuous : ContinuousOn
          (fun w : X F => (p, coordsX F w)) Set.univ := by fun_prop
      have hjointOnW : ContinuousOn
          (fun w : X F => iteratedFDeriv ℝ n joint (p, coordsX F w)) Set.univ :=
        (hderivJointContinuous n).comp hpairContinuous hpairMap
      have hcompContinuous : Continuous
          (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin n => Coord F × Coord F) ℂ =>
            D.compContinuousLinearMap
              (fun _ : Fin n => ContinuousLinearMap.inl ℝ (Coord F) (Coord F))) := by
        exact (isBoundedLinearMap_continuousMultilinearMap_comp_linear
          (𝕜 := ℝ) (ι := Fin n) (F := ℂ)
          (ContinuousLinearMap.inl ℝ (Coord F) (Coord F))).continuous
      have hcontinuousOn : ContinuousOn
          (fun w : X F =>
            (iteratedFDeriv ℝ n joint (p, coordsX F w)).compContinuousLinearMap
              (fun _ : Fin n => ContinuousLinearMap.inl ℝ (Coord F) (Coord F))) Set.univ :=
        hcompContinuous.comp_continuousOn hjointOnW
      have hcontinuous : Continuous (fun w : X F =>
          (iteratedFDeriv ℝ n joint (p, coordsX F w)).compContinuousLinearMap
            (fun _ : Fin n => ContinuousLinearMap.inl ℝ (Coord F) (Coord F))) :=
        continuousOn_univ.mp hcontinuousOn
      have heq : (fun w : X F =>
          iteratedFDeriv ℝ n (fun q => radialKernel F k₀ (ptX F q) w) p) =
        (fun w : X F =>
          (iteratedFDeriv ℝ n joint (p, coordsX F w)).compContinuousLinearMap
            (fun _ : Fin n => ContinuousLinearMap.inl ℝ (Coord F) (Coord F))) := by
        funext w
        exact hsectionDerivative n p hp w
      rw [heq]
      exact hcontinuous.aestronglyMeasurable
    · intro n p hp w hw
      exact hderivZero n p hp w hw
    · intro n
      by_cases hWempty : W = ∅
      · refine ⟨0, le_rfl, ?_⟩
        intro p hp w
        have hw : w ∉ W := by simp [hWempty]
        rw [hderivZero n p hp w hw]
        simp
      · have hWne : W.Nonempty := Set.nonempty_iff_ne_empty.mpr hWempty
        have hPne : P.Nonempty := by
          rcases hKne with ⟨p₀, hp₀⟩
          rcases hWne with ⟨w₀, hw₀⟩
          exact ⟨(p₀, coordsX F w₀),
            ⟨subset_closure (hKU hp₀), ⟨w₀, hw₀, rfl⟩⟩⟩
        have hnormContinuous : ContinuousOn
            (fun pq : Coord F × Coord F => ‖iteratedFDeriv ℝ n joint pq‖) S := by
          exact continuous_norm.comp_continuousOn (hderivJointContinuous n)
        obtain ⟨pq₀, hpq₀, hmax⟩ :=
          hPcompact.exists_isMaxOn hPne (hnormContinuous.mono hPsubset)
        let C : ℝ := ‖iteratedFDeriv ℝ n joint pq₀‖
        have hCnonneg : 0 ≤ C := norm_nonneg _
        have hLnorm :
            ‖ContinuousLinearMap.inl ℝ (Coord F) (Coord F)‖ ≤ 1 :=
          ContinuousLinearMap.norm_inl_le_one ℝ (Coord F) (Coord F)
        have hprodL :
            (∏ _i : Fin n, ‖ContinuousLinearMap.inl ℝ (Coord F) (Coord F)‖) ≤ 1 := by
          calc
            _ = ‖ContinuousLinearMap.inl ℝ (Coord F) (Coord F)‖ ^ n := by simp
            _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hLnorm
        refine ⟨C, hCnonneg, ?_⟩
        intro p hp w
        by_cases hw : w ∈ W
        · have hpair : (p, coordsX F w) ∈ P :=
            ⟨subset_closure hp, ⟨w, hw, rfl⟩⟩
          rw [hsectionDerivative n p hp w]
          calc
            _ ≤ ‖iteratedFDeriv ℝ n joint (p, coordsX F w)‖ *
                ∏ _i : Fin n, ‖ContinuousLinearMap.inl ℝ (Coord F) (Coord F)‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
            _ ≤ ‖iteratedFDeriv ℝ n joint (p, coordsX F w)‖ :=
              mul_le_of_le_one_right (norm_nonneg _) hprodL
            _ ≤ C := (isMaxOn_iff.mp hmax) (p, coordsX F w) hpair
        · rw [hderivZero n p hp w hw]
          simp [C]

end ArtinPrimitiveRoots.A1.Spec
