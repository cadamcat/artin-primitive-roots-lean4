import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.Theta.Eis

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- The classical value in coordinates, with the positive diagonal supplied by `Reduction`. -/
def cuspClassical (P : CoverPackage D S H A)
    (a : (InfinitePlace F → ℝ) → P.tc.G) (Ψ : P.tc.G → ℂ) (gj : P.tc.G)
    (z : ArtinPrimitiveRoots.A1.Spec.X F) : ℂ :=
  Ψ (nInf P (fun w => ArtinPrimitiveRoots.A1.Spec.horiz (z w)) *
    a (fun w => ArtinPrimitiveRoots.A1.Spec.height (z w)) * gj)

/-- Projective Iwasawa follows from equality of the corresponding hyperbolic points. -/
theorem cusp_arch_iwasawa (g : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (x x' : ℂ) (y y' : ℝ) (hy : 0 < y) (hy' : 0 < y')
    (hcoord : g • ArtinPrimitiveRoots.A1.Spec.pt x y = ArtinPrimitiveRoots.A1.Spec.pt x' y') :
    ∃ k : GL (Fin 2) ℂ, (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL g) : PGL2 ℂ) *
        QuotientGroup.mk (upperM ℂ x) *
        QuotientGroup.mk (diagM ℂ (Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne'))) =
      QuotientGroup.mk (upperM ℂ x') *
        QuotientGroup.mk (diagM ℂ (Units.mk0 (y' : ℂ) (Complex.ofReal_ne_zero.mpr hy'.ne'))) *
        QuotientGroup.mk k := by
  have hproj (u : ℂ) (v : ℝ) (hv : 0 < v) :
      (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat u v hv)) : PGL2 ℂ) =
      QuotientGroup.mk (upperM ℂ u) *
        QuotientGroup.mk (diagM ℂ (Units.mk0 (v : ℂ) (Complex.ofReal_ne_zero.mpr hv.ne'))) := by
    have hs : (Real.sqrt v : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
    have hs2 : (Real.sqrt v : ℂ) * (Real.sqrt v : ℂ) = (v : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt hv.le
    let c : ℂˣ := Units.mk0 (Real.sqrt v : ℂ) hs
    have he : Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.ptMat u v hv) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c =
        upperM ℂ u * diagM ℂ (Units.mk0 (v : ℂ) (Complex.ofReal_ne_zero.mpr hv.ne')) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.SpecialLinearGroup.toGL, ArtinPrimitiveRoots.A1.Spec.ptMat, upperM, diagM,
          Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, c, hs, hs2]
    have hc : Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈
        Subgroup.center (GL (Fin 2) ℂ) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    have hcq : (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) c) : PGL2 ℂ) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hc
    have heq := congrArg (fun t : GL (Fin 2) ℂ => (QuotientGroup.mk t : PGL2 ℂ)) he
    simpa only [QuotientGroup.mk_mul, hcq, mul_one] using heq
  have hq : (QuotientGroup.mk (g * ArtinPrimitiveRoots.A1.Spec.ptMat x y hy) :
      ArtinPrimitiveRoots.A1.Spec.H3) =
      QuotientGroup.mk (ArtinPrimitiveRoots.A1.Spec.ptMat x' y' hy') := by
    rw [ArtinPrimitiveRoots.A1.Spec.pt, ArtinPrimitiveRoots.A1.Spec.pt,
      dite_eq_left hy, dite_eq_left hy'] at hcoord
    change (QuotientGroup.mk (g * ArtinPrimitiveRoots.A1.Spec.ptMat x y hy) :
      ArtinPrimitiveRoots.A1.Spec.H3) =
      QuotientGroup.mk (ArtinPrimitiveRoots.A1.Spec.ptMat x' y' hy') at hcoord
    exact hcoord
  let kSL := (ArtinPrimitiveRoots.A1.Spec.ptMat x' y' hy')⁻¹ *
    (g * ArtinPrimitiveRoots.A1.Spec.ptMat x y hy)
  have hk : kSL ∈ ArtinPrimitiveRoots.A1.Spec.SU2 :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact hq.symm)
  refine ⟨Matrix.SpecialLinearGroup.toGL kSL, hk, ?_⟩
  calc
    _ = (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL g) : PGL2 ℂ) *
        QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL (ArtinPrimitiveRoots.A1.Spec.ptMat x y hy)) := by
      rw [mul_assoc, hproj]
    _ = QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL
        (g * ArtinPrimitiveRoots.A1.Spec.ptMat x y hy)) := by simp only [map_mul, QuotientGroup.mk_mul]
    _ = QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL
        (ArtinPrimitiveRoots.A1.Spec.ptMat x' y' hy' * kSL)) := by
      congr 2
      dsimp only [kSL]
      group
    _ = _ := by
      simp only [map_mul, QuotientGroup.mk_mul]
      rw [hproj]

/-- Archimedean Iwasawa transports the cusp integrand to one adelic unipotent orbit. -/
theorem classical_constTerm_eq_zero_part1 [IsTotallyComplex F]
    (P : CoverPackage D S H A) (a : (InfinitePlace F → ℝ) → P.tc.G)
    (ha : a = fun y => if hy : ∀ w, 0 < y w then
      ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w =>
        P.tc.aS (S.atComplex w (Units.mk0 ((y w : ℝ) : ℂ)
          (Complex.ofReal_ne_zero.mpr (hy w).ne')))).prod else 1)
    (Ψ : P.tc.G → ℂ) (gj : P.tc.G)
    (hgj : ∃ x : P.RP, P.q x = gj ∧ ∀ w, P.compC w x = 1)
    (hAut : ∀ γ g, Ψ (P.tc.rat γ * g) = Ψ g)
    (hInf : ∀ g, ∀ k ∈ {k | ∃ x : P.RP, P.q x = k ∧ (∀ v, P.compF v x = 1) ∧
      ∀ w, ∃ u : GL (Fin 2) ℂ, (u : Matrix (Fin 2) (Fin 2) ℂ) ∈
        Matrix.unitaryGroup (Fin 2) ℂ ∧ P.compC w x = QuotientGroup.mk u}, Ψ (g * k) = Ψ g)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) :
    ∃ g', ∀ x, cuspClassical P a Ψ gj (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) =
      Ψ (nInf P x * g') := by
  have hN (x : InfinitePlace F → ℂ) :
      ∃ n : P.RP, P.q n = nInf P x ∧ (∀ v, P.compF v n = 1) ∧
        ∀ w, P.compC w n = QuotientGroup.mk (upperM ℂ (x w)) := by
    obtain ⟨n, hq, hf, hc⟩ := P.nS_components (0, x)
    refine ⟨n, hq, ?_, hc⟩
    intro v
    rw [hf]
    split_ifs <;> simp
  have hA (t : InfinitePlace F → ℝ) (ht : ∀ w, 0 < t w) :
      ∃ b : P.RP, P.q b = a t ∧ (∀ v, P.compF v b = 1) ∧
        ∀ w, P.compC w b = QuotientGroup.mk
          (diagM ℂ (Units.mk0 (t w : ℂ) (Complex.ofReal_ne_zero.mpr (ht w).ne'))) := by
    let z (w : InfinitePlace F) : ℂˣ :=
      Units.mk0 (t w : ℂ) (Complex.ofReal_ne_zero.mpr (ht w).ne')
    choose b hq hf hc using fun w => P.aS_components (S.atComplex w (z w))
    have hu (v : S.Sf) (w : InfinitePlace F) : S.compU v (S.atComplex w (z w)) = 1 := by
      rfl
    have hbF (w : InfinitePlace F) (v : FinPlace F) : P.compF v (b w) = 1 := by
      rw [hf]
      split_ifs <;> simp [hu, (P.loc v).a_one]
    let bAll := ((Finset.univ : Finset (InfinitePlace F)).toList.map b).prod
    refine ⟨bAll, ?_, ?_, ?_⟩
    · rw [ha]
      simp only [dite_eq_left ht]
      simp only [bAll, map_list_prod, List.map_map, Function.comp_def, hq]
      rfl
    · intro v
      simp only [bAll, map_list_prod, List.map_map, Function.comp_def]
      apply List.prod_eq_one
      intro k hk
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hk
      exact hbF w v
    · intro w
      have hcSelf : S.compC w (S.atComplex w (z w)) = z w := by
        ext
        simp [SData.compC, SData.atComplex]
      have hcOther (w' : InfinitePlace F) (hne : w' ≠ w) :
          S.compC w (S.atComplex w' (z w')) = 1 := by
        ext
        simp [SData.compC, SData.atComplex, Function.update_of_ne hne.symm]
      have hother : ∀ w' : InfinitePlace F, w' ≠ w →
          w' ∈ (Finset.univ : Finset (InfinitePlace F)).toList → P.compC w (b w') = 1 := by
        intro w' hne _
        rw [hc, hcOther w' hne]
        have hd : diagM ℂ (1 : ℂˣ) = 1 := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [diagM]
        rw [hd, QuotientGroup.mk_one]
      calc
        P.compC w bAll = ((Finset.univ : Finset (InfinitePlace F)).toList.map
          (fun w' => P.compC w (b w'))).prod := by
            simp only [bAll, map_list_prod, List.map_map, Function.comp_def]
        _ = P.compC w (b w) := by
          have hcount : List.count w (Finset.univ : Finset (InfinitePlace F)).toList = 1 :=
            List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)
          simpa only [hcount, pow_one] using
            List.prod_map_eq_pow_single w (fun w' => P.compC w (b w')) hother
        _ = _ := by rw [hc, hcSelf]
  have hcomm (f b : P.RP) (hf : ∀ w, P.compC w f = 1) (hb : ∀ v, P.compF v b = 1) :
      f * b = b * f := by
    apply P.comp_ext
    · intro v
      simp only [map_mul, hb, mul_one, one_mul]
    · intro w
      simp only [map_mul, hf, mul_one, one_mul]
  let r := P.ratRP (Matrix.SpecialLinearGroup.toGL τ)
  obtain ⟨tf, htfF, htfC⟩ := P.comp_surj (fun v => P.compF v r) (fun _ => 1)
    (P.comp_restricted r)
  let ti := tf⁻¹ * r
  have htiF (v : FinPlace F) : P.compF v ti = 1 := by
    simp only [ti, map_mul, map_inv, htfF, inv_mul_cancel]
  have hmap (w : InfinitePlace F) :
      Matrix.GeneralLinearGroup.map w.embedding (Matrix.SpecialLinearGroup.toGL τ) =
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map w.embedding τ) := by
    ext i j
    rfl
  have htiC (w : InfinitePlace F) : P.compC w ti = QuotientGroup.mk
      (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map w.embedding τ)) := by
    simp only [ti, map_mul, map_inv, htfC, inv_one, one_mul,
      r, P.compC_ratRP, hmap]
  have hrat : P.tc.rat (Matrix.SpecialLinearGroup.toGL τ) = P.q ti * P.q tf := by
    calc
      _ = P.q r := (P.q_ratRP _).symm
      _ = P.q (tf * ti) := by
        congr 1
        dsimp only [ti]
        group
      _ = P.q (ti * tf) := congrArg P.q (hcomm tf ti htfC htiF)
      _ = _ := map_mul _ _ _
  obtain ⟨j, hj, hjC⟩ := hgj
  obtain ⟨ay, hay, hayF, hayC⟩ := hA y hy
  refine ⟨a y * (P.q tf)⁻¹ * gj, ?_⟩
  intro x
  let z := τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y
  let x' := fun w => ArtinPrimitiveRoots.A1.Spec.horiz (z w)
  let y' := fun w => ArtinPrimitiveRoots.A1.Spec.height (z w)
  have hy' : ∀ w, 0 < y' w := by
    intro w
    change 0 < ArtinPrimitiveRoots.A1.Spec.height (z w)
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos _
  obtain ⟨nx, hnx, hnxF, hnxC⟩ := hN x
  obtain ⟨nx', hnx', hnx'F, hnx'C⟩ := hN x'
  obtain ⟨ay', hay', hay'F, hay'C⟩ := hA y' hy'
  have hcoord (w : InfinitePlace F) :
      Matrix.SpecialLinearGroup.map w.embedding τ • ArtinPrimitiveRoots.A1.Spec.pt (x w) (y w) =
        ArtinPrimitiveRoots.A1.Spec.pt (x' w) (y' w) := by
    change z w = ArtinPrimitiveRoots.A1.Spec.pt
      (ArtinPrimitiveRoots.A1.Spec.horiz (z w)) (ArtinPrimitiveRoots.A1.Spec.height (z w))
    exact (ArtinPrimitiveRoots.A1.Spec.pt_horiz_height _).symm
  have hiwa (w : InfinitePlace F) := cusp_arch_iwasawa
    (Matrix.SpecialLinearGroup.map w.embedding τ) (x w) (x' w) (y w) (y' w)
      (hy w) (hy' w) (hcoord w)
  let k (w : InfinitePlace F) : GL (Fin 2) ℂ := Classical.choose (hiwa w)
  have hk (w : InfinitePlace F) : (k w : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Matrix.unitaryGroup (Fin 2) ℂ := (Classical.choose_spec (hiwa w)).1
  have hki (w : InfinitePlace F) := (Classical.choose_spec (hiwa w)).2
  obtain ⟨kinf, hkinfF, hkinfC⟩ := P.comp_surj (fun _ => 1)
    (fun w => QuotientGroup.mk (k w)) (by simp)
  have hI : ti * nx * ay = nx' * ay' * kinf := by
    apply P.comp_ext
    · intro v
      simp only [map_mul, htiF, hnxF, hayF, hnx'F, hay'F, hkinfF, one_mul]
    · intro w
      simpa only [map_mul, htiC, hnxC, hayC, hnx'C, hay'C, hkinfC] using hki w
  have hIG : P.q ti * nInf P x * a y = nInf P x' * a y' * P.q kinf := by
    simpa only [map_mul, hnx, hay, hnx', hay'] using congrArg P.q hI
  have hcompact : P.q kinf ∈ {g | ∃ b : P.RP, P.q b = g ∧
      (∀ v, P.compF v b = 1) ∧ ∀ w, ∃ k : GL (Fin 2) ℂ,
      (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
        P.compC w b = QuotientGroup.mk k} :=
    ⟨kinf, rfl, hkinfF, fun w => ⟨k w, hk w, hkinfC w⟩⟩
  have hKJ : P.q kinf * gj = gj * P.q kinf := by
    rw [← hj]
    simpa only [map_mul] using congrArg P.q (hcomm j kinf hjC hkinfF).symm
  have hTN : P.q tf * nInf P x = nInf P x * P.q tf := by
    rw [← hnx]
    simpa only [map_mul] using congrArg P.q (hcomm tf nx htfC hnxF)
  have hTA : P.q tf * a y = a y * P.q tf := by
    rw [← hay]
    simpa only [map_mul] using congrArg P.q (hcomm tf ay htfC hayF)
  have hTNA : P.q tf * (nInf P x * a y) = (nInf P x * a y) * P.q tf := by
    rw [← mul_assoc, hTN, mul_assoc, hTA, ← mul_assoc]
  have heq : P.tc.rat (Matrix.SpecialLinearGroup.toGL τ) *
      (nInf P x * a y * (P.q tf)⁻¹ * gj) = P.q ti * nInf P x * a y * gj := by
    rw [hrat]
    calc
      _ = P.q ti * (P.q tf * (nInf P x * a y)) * (P.q tf)⁻¹ * gj := by group
      _ = P.q ti * ((nInf P x * a y) * P.q tf) * (P.q tf)⁻¹ * gj := by rw [hTNA]
      _ = _ := by group
  have haut := hAut (Matrix.SpecialLinearGroup.toGL τ)
    (nInf P x * a y * (P.q tf)⁻¹ * gj)
  rw [heq] at haut
  change Ψ (nInf P x' * a y' * gj) = Ψ (nInf P x * (a y * (P.q tf)⁻¹ * gj))
  calc
    _ = Ψ ((nInf P x' * a y' * gj) * P.q kinf) := (hInf _ _ hcompact).symm
    _ = Ψ (P.q ti * nInf P x * a y * gj) := by
      congr 1
      rw [hIG]
      calc
        _ = (nInf P x' * a y') * (gj * P.q kinf) := by group
        _ = (nInf P x' * a y') * (P.q kinf * gj) := by rw [hKJ]
        _ = _ := by group
    _ = Ψ (nInf P x * a y * (P.q tf)⁻¹ * gj) := haut
    _ = _ := by congr 1; group

/-- A common adapted ideal is a finite-index sublattice of the cusp translations. -/
theorem th_cusp_part2 [IsTotallyComplex F] (P : CoverPackage D S H A)
    (Ψ : P.tc.G → ℂ) (g' : P.tc.G)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F))) (hfinite : Γ.FiniteIndex)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F)
    (hlevel : ∀ g : P.tc.G, ∃ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F,
      𝔞 ≠ 0 ∧ ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        Ψ (h * (g⁻¹ * nFin P ξ * g)) = Ψ h) :
    ∃ (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (P₀ Pτ : Set (InfinitePlace F → ℂ)),
      𝔞 ≠ 0 ∧
      (∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
        Ψ (h * (g'⁻¹ * nFin P ξ * g')) = Ψ h) ∧
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom ≤
        ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ) ∧
      (((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom).relIndex
        (ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ) ≠ 0) ∧
      IsAddFundamentalDomain ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom)
        P₀ volume ∧ Bornology.IsBounded P₀ ∧ (0 < (volume P₀).toReal) ∧
      IsAddFundamentalDomain (ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ) Pτ volume := by
  sorry

/-- Constant-term integrands are periodic under the rational cusp translations. -/
theorem th_cusp_periodic [IsTotallyComplex F] (P : CoverPackage D S H A)
    (a : (InfinitePlace F → ℝ) → P.tc.G) (Ψ : P.tc.G → ℂ) (gj : P.tc.G)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)))
    (hΓ : ∀ γ ∈ Γ, ∀ z, cuspClassical P a Ψ gj (γ • z) = cuspClassical P a Ψ gj z)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) :
    ∀ μ ∈ ArtinPrimitiveRoots.A1.Spec.cuspTranslations F Γ τ, ∀ x,
      cuspClassical P a Ψ gj (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F (μ + x) y) =
        cuspClassical P a Ψ gj (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) := by
  sorry

/-- A zero integral descends from a finite-index period sublattice, including nonintegrable functions. -/
theorem th_cusp_part3 (Λ₀ Λ : AddSubgroup (InfinitePlace F → ℂ))
    (hle : Λ₀ ≤ Λ) (hindex : Λ₀.relIndex Λ ≠ 0)
    (P₀ Pτ : Set (InfinitePlace F → ℂ))
    (hP₀ : IsAddFundamentalDomain Λ₀ P₀ volume)
    (hPτ : IsAddFundamentalDomain Λ Pτ volume)
    (f : (InfinitePlace F → ℂ) → ℂ)
    (hf : ∀ μ ∈ Λ, ∀ x, f (μ + x) = f x) (hzero : ∫ x in P₀, f x = 0) :
    ∫ x in Pτ, f x = 0 := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
