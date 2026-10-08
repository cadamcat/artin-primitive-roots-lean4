import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.CongruenceShrinking

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private def diagonalHom : Fˣ →* GL (Fin 2) F where
  toFun := diagGL
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL]
  map_mul' x y := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL]

omit [NumberField F] in
private theorem diagonal_inv (δ : Fˣ) : (diagGL δ)⁻¹ = diagGL δ⁻¹ :=
  (diagonalHom.map_inv δ).symm

omit [NumberField F] in
private theorem diagonal_det (δ : Fˣ) : Matrix.GeneralLinearGroup.det (diagGL δ) = δ := by
  apply Units.ext
  change Matrix.det !![(δ : F), 0; 0, 1] = (δ : F)
  simp [Matrix.det_fin_two]

private theorem diagonal_mem (P : CoverPackage D S H A) (G : GlobalDatum P) (δ : Fˣ) :
    diagGL δ ∈ Bstar G ↔ δ ∈ G.Δ := by
  change (0 = (0 : F) ∧ ∃ ν ∈ G.Δ, (δ : F) = (ν : F) * 1) ↔ δ ∈ G.Δ
  constructor
  · rintro ⟨_, ν, hν, hδ⟩
    have heq : δ = ν := Units.ext (by simpa using hδ)
    simpa only [heq] using hν
  · intro hδ
    exact ⟨rfl, δ, hδ, (mul_one _).symm⟩

/-- Chosen special-linear Borel representatives give the torus fiber of the theta quotient. -/
theorem cusp_fiber_equiv (P : CoverPackage D S H A) (G : GlobalDatum P)
    (R : Type) (r : R → Matrix.SpecialLinearGroup (Fin 2) F)
    (hr : Function.Bijective (fun z =>
      Quotient.mk (QuotientGroup.rightRel (Spec.borelSL F)) (r z))) :
    ∃ e : Quotient (QuotientGroup.rightRel (Bstar G)) ≃ (Fˣ ⧸ G.Δ) × R,
      ∀ p, e.symm p = Quotient.mk _ (diagGL p.1.out * (r p.2).toGL) := by
  let Q := Quotient (QuotientGroup.rightRel (Bstar G))
  have htorus (z : R) (ν ν' : Fˣ)
      (hν : QuotientGroup.leftRel G.Δ ν ν') :
      (Quotient.mk _ (diagGL ν * (r z).toGL) : Q) =
        Quotient.mk _ (diagGL ν' * (r z).toGL) := by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    have heq : (diagGL ν' * (r z).toGL) * (diagGL ν * (r z).toGL)⁻¹ =
        diagGL (ν' * ν⁻¹) := by
      rw [show diagGL (ν' * ν⁻¹) = diagGL ν' * (diagGL ν)⁻¹ from
        (diagonalHom.map_mul ν' ν⁻¹).trans (by
          change diagGL ν' * diagGL ν⁻¹ = _
          rw [← diagonal_inv])]
      group
    rw [heq, diagonal_mem P G]
    simpa only [mul_comm] using QuotientGroup.leftRel_apply.mp hν
  let f : (Fˣ ⧸ G.Δ) × R → Q := fun p =>
    Quotient.lift (fun ν : Fˣ => Quotient.mk _ (diagGL ν * (r p.2).toGL))
      (htorus p.2) p.1
  have fout (p : (Fˣ ⧸ G.Δ) × R) :
      f p = Quotient.mk _ (diagGL p.1.out * (r p.2).toGL) := by
    change Quotient.lift _ _ p.1 = _
    conv_lhs => rw [← Quotient.out_eq p.1]
    rfl
  have hinj : Function.Injective f := by
    rintro ⟨δ, z⟩ ⟨δ', z'⟩ h
    rw [fout, fout] at h
    have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    let M : Matrix.SpecialLinearGroup (Fin 2) F := r z' * (r z)⁻¹
    have heq : (diagGL δ'.out * (r z').toGL) * (diagGL δ.out * (r z).toGL)⁻¹ =
        diagGL δ'.out * M.toGL * diagGL (δ.out)⁻¹ := by
      dsimp only [M]
      rw [map_mul, map_inv, ← diagonal_inv]
      group
    have hlow := hrel.1
    rw [heq] at hlow
    change ((diagGL δ'.out : Matrix (Fin 2) (Fin 2) F) *
      (M : Matrix (Fin 2) (Fin 2) F) * (diagGL (δ.out)⁻¹ : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0 at hlow
    have hM : M ∈ Spec.borelSL F := by
      change M 1 0 = 0
      simpa [diagGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hlow
    have hz : z = z' := hr.1 (Quotient.sound (QuotientGroup.rightRel_apply.mpr hM))
    subst z'
    have heq' : (diagGL δ'.out * (r z).toGL) * (diagGL δ.out * (r z).toGL)⁻¹ =
        diagGL (δ'.out * (δ.out)⁻¹) := by
      rw [show diagGL (δ'.out * (δ.out)⁻¹) = diagGL δ'.out * (diagGL δ.out)⁻¹ from
        (diagonalHom.map_mul δ'.out (δ.out)⁻¹).trans (by
          change diagGL δ'.out * diagGL (δ.out)⁻¹ = _
          rw [← diagonal_inv])]
      group
    have hδ : δ = δ' := by
      have hd : δ'.out * (δ.out)⁻¹ ∈ G.Δ := by
        rw [heq'] at hrel
        exact (diagonal_mem P G _).mp hrel
      have hq : (Quotient.mk _ δ.out : Fˣ ⧸ G.Δ) = Quotient.mk _ δ'.out := by
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        simpa only [mul_comm] using hd
      simpa only [Quotient.out_eq] using hq
    exact Prod.ext hδ rfl
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := Quotient.mk_surjective q
    let d := Matrix.GeneralLinearGroup.det g
    have hdet : diagGL d⁻¹ * g ∈ Matrix.GeneralLinearGroup.det.ker := by
      change Matrix.GeneralLinearGroup.det (diagGL d⁻¹ * g) = 1
      rw [map_mul, diagonal_det]
      exact inv_mul_cancel d
    have hrange : diagGL d⁻¹ * g ∈ Matrix.SpecialLinearGroup.toGL.range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hdet
    obtain ⟨a, ha⟩ := hrange
    obtain ⟨z, hz⟩ := hr.2 (Quotient.mk _ a)
    have htri : a * (r z)⁻¹ ∈ Spec.borelSL F :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hz)
    have hg : g = diagGL d * a.toGL := by
      rw [ha, ← diagonal_inv]
      group
    let b : GL (Fin 2) F := g * (r z).toGL⁻¹
    have hb : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have heq : b = diagGL d * (a * (r z)⁻¹).toGL := by
        dsimp only [b]
        rw [hg, map_mul, map_inv]
        group
      rw [heq]
      change ((diagGL d : Matrix (Fin 2) (Fin 2) F) *
        (a * (r z)⁻¹ : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0
      change (a * (r z)⁻¹) 1 0 = 0 at htri
      simpa [diagGL, Matrix.mul_apply, Fin.sum_univ_two] using htri
    have hdiag0 : (b : Matrix (Fin 2) (Fin 2) F) 0 0 *
        (b : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      simpa only [Matrix.det_fin_two, hb, mul_zero, sub_zero] using
        Matrix.GeneralLinearGroup.det_ne_zero b
    have hb00 := (mul_ne_zero_iff.mp hdiag0).1
    have hb11 := (mul_ne_zero_iff.mp hdiag0).2
    let ν : Fˣ := Units.mk0 ((b : Matrix (Fin 2) (Fin 2) F) 0 0 /
      (b : Matrix (Fin 2) (Fin 2) F) 1 1) (div_ne_zero hb00 hb11)
    refine ⟨⟨Quotient.mk _ ν, z⟩, ?_⟩
    change Quotient.mk _ (diagGL ν * (r z).toGL) = Quotient.mk _ g
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    have heq : g * (diagGL ν * (r z).toGL)⁻¹ = b * diagGL ν⁻¹ := by
      dsimp only [b]
      rw [← diagonal_inv]
      group
    rw [heq]
    change ((b : Matrix (Fin 2) (Fin 2) F) *
      (diagGL ν⁻¹ : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0 ∧ _
    constructor
    · simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two, hb]
    · refine ⟨1, G.Δ.one_mem, ?_⟩
      simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two, ν]
      field_simp
  refine ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).symm, ?_⟩
  exact fout

end ArtinPrimitiveRoots.A1.Theta
