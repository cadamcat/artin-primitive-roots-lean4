import ArtinPrimitiveRoots.Theta.LocalInt

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.TH_WHITTAKER

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

private theorem gl_bruhat_big (g : GL (Fin 2) (v.adicCompletion F))
    (hc : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0) :
    ∃ r : (v.adicCompletion F)ˣ, ∃ x : v.adicCompletion F,
      ∃ y : (v.adicCompletion F)ˣ, ∃ t : v.adicCompletion F,
        g = Matrix.GeneralLinearGroup.scalar (Fin 2) r *
          (upperM _ x * diagM _ y * weylM _ * upperM _ t) := by
  let a : v.adicCompletion F :=
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0
  let b : v.adicCompletion F :=
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1
  let c : v.adicCompletion F :=
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
  let d : v.adicCompletion F :=
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
  have hc' : c ≠ 0 := hc
  let x := a / c
  let t := d / c
  let yy := b / c - (a / c) * (d / c)
  have hyy : yy ≠ 0 := by
    intro hy
    have hdet : a * d - b * c ≠ 0 := by
      simpa [a, b, c, d, Matrix.det_fin_two] using g.det_ne_zero
    dsimp [yy] at hy
    field_simp at hy
    simp at hy
    have hzero : a * d - b * c = 0 := by
      calc
        a * d - b * c = -(b * c - a * d) := by ring
        _ = 0 := by rw [hy]; simp
    exact hdet hzero
  let y : (v.adicCompletion F)ˣ := Units.mk0 yy hyy
  refine ⟨Units.mk0 c hc', x, y, t, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · have h : a = c * x := by dsimp [x]; field_simp [hc']
    simpa [a, b, c, d, x, y, t, yy, upperM, diagM, weylM,
      Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply] using
        congrArg (fun z : v.adicCompletion F => z.toCompletion) h
  · have h : b = c * (x * t + yy) := by
      dsimp [x, t, yy]
      field_simp [hc']
      ring
    simpa [a, b, c, d, x, y, t, yy, upperM, diagM, weylM,
      Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply] using
        congrArg (fun z : v.adicCompletion F => z.toCompletion) h
  · have h : c = c := rfl
    simpa [a, b, c, d, x, y, t, yy, upperM, diagM, weylM,
      Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply] using
        congrArg (fun z : v.adicCompletion F => z.toCompletion) h
  · have h : d = c * t := by dsimp [t]; field_simp [hc']
    simpa [a, b, c, d, x, y, t, yy, upperM, diagM, weylM,
      Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply] using
        congrArg (fun z : v.adicCompletion F => z.toCompletion) h

private theorem gl_bruhat_small (g : GL (Fin 2) (v.adicCompletion F))
    (hc : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0) :
    ∃ r : (v.adicCompletion F)ˣ, ∃ x : v.adicCompletion F,
      ∃ y : (v.adicCompletion F)ˣ,
        g = Matrix.GeneralLinearGroup.scalar (Fin 2) r * (upperM _ x * diagM _ y) := by
  let a : v.adicCompletion F :=
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0
  let b : v.adicCompletion F :=
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1
  let c : v.adicCompletion F :=
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
  let d : v.adicCompletion F :=
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
  have hc' : c = 0 := hc
  have hd : d ≠ 0 := by
    intro hd
    apply g.det_ne_zero
    rw [Matrix.det_fin_two]
    simp [a, b, c, d, hc', hd]
  have ha : a ≠ 0 := by
    intro ha
    apply g.det_ne_zero
    rw [Matrix.det_fin_two]
    simp [a, b, c, d, hc', ha]
  let x := b / d
  let yy := a / d
  have hyy : yy ≠ 0 := div_ne_zero ha hd
  let y : (v.adicCompletion F)ˣ := Units.mk0 yy hyy
  refine ⟨Units.mk0 d hd, x, y, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · have h : a = d * yy := by dsimp [yy]; field_simp [hd]
    simpa [a, b, c, d, x, y, yy, upperM, diagM,
      Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply] using
        congrArg (fun z : v.adicCompletion F => z.toCompletion) h
  · have h : b = d * x := by dsimp [x]; field_simp [hd]
    simpa [a, b, c, d, x, y, yy, upperM, diagM,
      Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply] using
        congrArg (fun z : v.adicCompletion F => z.toCompletion) h
  · have h : c = 0 := hc'
    simpa [a, b, c, d, x, y, yy, upperM, diagM,
      Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply] using
        congrArg (fun z : v.adicCompletion F => z.toCompletion) h
  · have h : d = d := rfl
    simpa [a, b, c, d, x, y, yy, upperM, diagM,
      Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply] using
        congrArg (fun z : v.adicCompletion F => z.toCompletion) h

private abbrev pglMk (M : GL (Fin 2) (v.adicCompletion F)) :
    PGL2 (v.adicCompletion F) := QuotientGroup.mk M

private theorem quotient_scalar_mul (r : (v.adicCompletion F)ˣ)
    (M : GL (Fin 2) (v.adicCompletion F)) :
    pglMk (Matrix.GeneralLinearGroup.scalar (Fin 2) r * M) = pglMk M := by
  have hc : Matrix.GeneralLinearGroup.scalar (Fin 2) r ∈
      Subgroup.center (GL (Fin 2) (v.adicCompletion F)) := by
    rw [Subgroup.mem_center_iff]
    intro X
    exact (Matrix.GeneralLinearGroup.scalar_commute r X).symm
  have hmk : pglMk (Matrix.GeneralLinearGroup.scalar (Fin 2) r) = 1 :=
    (QuotientGroup.eq_one_iff (Matrix.GeneralLinearGroup.scalar (Fin 2) r)).2 hc
  calc
    pglMk (Matrix.GeneralLinearGroup.scalar (Fin 2) r * M) =
        pglMk (Matrix.GeneralLinearGroup.scalar (Fin 2) r) * pglMk M := by
          exact QuotientGroup.mk_mul
            (Subgroup.center (GL (Fin 2) (v.adicCompletion F))) _ _
    _ = pglMk M := by rw [hmk]; simp

private theorem lift_eq_of_pr_eq (L : FinLocalCover D H v) {g h : L.L}
    (hp : L.pr g = L.pr h) : ∃ ζ, g = L.z ζ * h := by
  have hk : L.pr (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hp]
    exact mul_inv_cancel _
  have hm : g * h⁻¹ ∈ L.pr.ker := by
    change L.pr (g * h⁻¹) = 1
    exact hk
  rw [L.pr_ker] at hm
  rcases hm with ⟨ζ, hζ⟩
  refine ⟨ζ, ?_⟩
  calc
    g = (g * h⁻¹) * h := by group
    _ = L.z ζ * h := by rw [hζ]

theorem cover_bruhat (L : FinLocalCover D H v) (g : L.L) :
    (∃ x ζ y t, g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
        L.n (Multiplicative.ofAdd t)) ∨
    (∃ x ζ y, g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y) := by
  obtain ⟨M, hM⟩ := QuotientGroup.mk_surjective (L.pr g)
  by_cases hc : (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
  · obtain ⟨r, x, y, hfactor⟩ := gl_bruhat_small M hc
    have hclass : pglMk M = pglMk (upperM _ x * diagM _ y) := by
      calc
        pglMk M =
            pglMk (Matrix.GeneralLinearGroup.scalar (Fin 2) r *
              (upperM _ x * diagM _ y)) := by rw [hfactor]
        _ = pglMk (upperM _ x * diagM _ y) := quotient_scalar_mul r _
    let p : L.L := L.n (Multiplicative.ofAdd x) * L.a y
    have hp : L.pr p = L.pr g := by
      calc
        L.pr p = pglMk (upperM _ x * diagM _ y) := by
          simp [p, L.pr_n, L.pr_a]
        _ = QuotientGroup.mk M := hclass.symm
        _ = L.pr g := hM
    obtain ⟨ζ, hζ⟩ := lift_eq_of_pr_eq L hp.symm
    refine Or.inr ⟨x, ζ, y, ?_⟩
    calc
      g = L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y) := hζ
      _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y := by
        rw [show L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y) =
          (L.z ζ * L.n (Multiplicative.ofAdd x)) * L.a y by group]
        rw [L.z_central ζ (L.n (Multiplicative.ofAdd x))]
  · obtain ⟨r, x, y, t, hfactor⟩ := gl_bruhat_big M hc
    have hclass : pglMk M =
        pglMk (upperM _ x * diagM _ y * weylM _ * upperM _ t) := by
      calc
        pglMk M =
            pglMk (Matrix.GeneralLinearGroup.scalar (Fin 2) r *
              (upperM _ x * diagM _ y * weylM _ * upperM _ t)) := by rw [hfactor]
        _ = pglMk (upperM _ x * diagM _ y * weylM _ * upperM _ t) :=
          quotient_scalar_mul r _
    let p : L.L := L.n (Multiplicative.ofAdd x) * L.a y * L.w *
      L.n (Multiplicative.ofAdd t)
    have hp : L.pr p = L.pr g := by
      calc
        L.pr p = pglMk (upperM _ x * diagM _ y * weylM _ * upperM _ t) := by
          simp [p, L.pr_n, L.pr_a, L.pr_w]
        _ = QuotientGroup.mk M := hclass.symm
        _ = L.pr g := hM
    obtain ⟨ζ, hζ⟩ := lift_eq_of_pr_eq L hp.symm
    refine Or.inl ⟨x, ζ, y, t, ?_⟩
    calc
      g = L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) := hζ
      _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t) := by
        rw [show L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) =
          (L.z ζ * L.n (Multiplicative.ofAdd x)) * L.a y * L.w *
            L.n (Multiplicative.ofAdd t) by group]
        rw [L.z_central ζ (L.n (Multiplicative.ofAdd x))]

end ArtinPrimitiveRoots.Proofs.TH_WHITTAKER

end
