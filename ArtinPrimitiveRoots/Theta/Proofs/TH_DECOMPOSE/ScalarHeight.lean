import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.ArchHeight

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Moving only the complex coordinates scales the scalar by the hyperbolic height ratio. -/
theorem scalarOf_rational_height_ratio [IsTotallyComplex F]
    (P : CoverPackage D S H A) (G : GlobalDatum P) {s : ℂ}
    (Fs : GlobalSection P G s) (hC : ∀ w, Fs.fC w = sphC s)
    (a : (InfinitePlace F → ℝ) → P.tc.G)
    (ha : a = fun y => if hy : ∀ w, 0 < y w then
      ((Finset.univ : Finset (InfinitePlace F)).toList.map fun w =>
        P.tc.aS (S.atComplex w (Units.mk0 ((y w : ℝ) : ℂ)
          (Complex.ofReal_ne_zero.mpr (hy w).ne')))).prod else 1)
    (gj : P.tc.G) (hgj : ∃ r : P.RP, P.q r = gj ∧ ∀ w, P.compC w r = 1)
    (δ : Fˣ) (τ : Matrix.SpecialLinearGroup (Fin 2) F)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    scalarOf P G Fs.f Fs.fC
      (P.tc.rat (diagGL δ * Matrix.SpecialLinearGroup.toGL τ) * (nInf P x * a y * gj)) =
      (scalarOf P G Fs.f Fs.fC
        (P.tc.rat (diagGL δ * Matrix.SpecialLinearGroup.toGL τ) * gj) /
        (ArtinPrimitiveRoots.A1.Spec.normHeight F
          (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F (fun _ => 0) (fun _ => 1)) : ℂ) ^
            (1 + 2 * s)) *
      (ArtinPrimitiveRoots.A1.Spec.normHeight F
        (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) : ℂ) ^ (1 + 2 * s) := by
  have hN : ∃ n : P.RP, P.q n = nInf P x ∧ (∀ v, P.compF v n = 1) ∧
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
    let b (w : InfinitePlace F) : P.RP :=
      Classical.choose (P.aS_components (S.atComplex w (z w)))
    have hq (w : InfinitePlace F) :=
      (Classical.choose_spec (P.aS_components (S.atComplex w (z w)))).1
    have hf (w : InfinitePlace F) :=
      (Classical.choose_spec (P.aS_components (S.atComplex w (z w)))).2.1
    have hc (w : InfinitePlace F) :=
      (Classical.choose_spec (P.aS_components (S.atComplex w (z w)))).2.2
    have hu (v : S.Sf) (w : InfinitePlace F) : S.compU v (S.atComplex w (z w)) = 1 := by
      rfl
    have hbF (w : InfinitePlace F) (v : FinPlace F) : P.compF v (b w) = 1 := by
      rw [hf]
      split_ifs <;> simp [hu, (P.loc v).a_one]
    let bAll := ((Finset.univ : Finset (InfinitePlace F)).toList.map b).prod
    refine ⟨bAll, ?_, ?_, ?_⟩
    · rw [ha]
      simp only [dite_eq_left ht]
      simp only [bAll, map_list_prod, List.map_map, Function.comp_def, b, hq]
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
  obtain ⟨n, hnq, hnF, hnC⟩ := hN
  obtain ⟨b, hbq, hbF, hbC⟩ := hA y hy
  obtain ⟨j, hjq, hjC⟩ := hgj
  let M := diagGL δ * Matrix.SpecialLinearGroup.toGL τ
  let r := P.ratRP M
  have hqxy : P.q (r * (n * b * j)) =
      P.tc.rat M * (nInf P x * a y * gj) := by
    simp only [map_mul, r, P.q_ratRP, hnq, hbq, hjq]
  have hqbase : P.q (r * j) = P.tc.rat M * gj := by
    simp only [map_mul, r, P.q_ratRP, hjq]
  have hfin : (∏ᶠ v, G.lam v (Fs.f v (P.compF v (r * (n * b * j))))) =
      ∏ᶠ v, G.lam v (Fs.f v (P.compF v (r * j))) := by
    apply finprod_congr
    intro v
    simp only [map_mul, hnF, hbF, one_mul]
  have harch : (∏ w, Fs.fC w (P.compC w (r * (n * b * j)))) =
      (∏ w : InfinitePlace F,
        (Complex.normSq (w.embedding (δ : F)) : ℂ) ^ ((1 : ℂ) / 2 + s)) *
        (Spec.normHeight F (τ • Spec.ptX' F x y) : ℂ) ^ (1 + 2 * s) := by
    calc
      _ = ∏ w : InfinitePlace F, sphC s
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding M) *
            QuotientGroup.mk (upperM ℂ (x w)) *
            QuotientGroup.mk (diagM ℂ (Units.mk0 (y w : ℂ)
              (Complex.ofReal_ne_zero.mpr (hy w).ne')))) := by
        apply Finset.prod_congr rfl
        intro w _
        simp only [map_mul, hC, r, P.compC_ratRP, hnC, hbC, hjC, mul_one,
          mul_assoc]
      _ = _ := sphC_rational_arch_product s δ τ x y hy
  have hup0 : upperM ℂ 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperM]
  have hdiag1 : diagM ℂ (1 : ℂˣ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagM]
  have harchbase : (∏ w, Fs.fC w (P.compC w (r * j))) =
      (∏ w : InfinitePlace F,
        (Complex.normSq (w.embedding (δ : F)) : ℂ) ^ ((1 : ℂ) / 2 + s)) *
        (Spec.normHeight F (τ • Spec.ptX' F (fun _ => 0) (fun _ => 1)) : ℂ) ^
          (1 + 2 * s) := by
    have he := sphC_rational_arch_product s δ τ
      (fun _ => 0) (fun _ => 1) (fun _ => zero_lt_one)
    simp only [Complex.ofReal_one, Units.mk0_one, hup0, hdiag1,
      QuotientGroup.mk_one, mul_one] at he
    calc
      _ = ∏ w : InfinitePlace F, sphC s
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding M)) := by
        apply Finset.prod_congr rfl
        intro w _
        simp only [map_mul, hC, r, P.compC_ratRP, hjC, mul_one]
      _ = _ := he
  have hbasepos : 0 < Spec.normHeight F
      (τ • Spec.ptX' F (fun _ => 0) (fun _ => 1)) := by
    unfold Spec.normHeight
    apply Finset.prod_pos
    intro w _
    rw [Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos _
  have hbasene : (Spec.normHeight F
      (τ • Spec.ptX' F (fun _ => 0) (fun _ => 1)) : ℂ) ^ (1 + 2 * s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hbasepos.ne'))
  change scalarOf P G Fs.f Fs.fC (P.tc.rat M * (nInf P x * a y * gj)) = _
  rw [← hqxy, (scalarOf_q P G Fs (r * (n * b * j))).2, hfin, harch,
    ← hqbase, (scalarOf_q P G Fs (r * j)).2, harchbase]
  simp only [← mul_assoc, mul_div_cancel_right₀ _ hbasene]

end ArtinPrimitiveRoots.A1.Theta
