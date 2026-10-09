import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_right_of_scalar_invariant

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Spherical archimedean sections give right maximal-compact invariance
of the Eisenstein residue. -/
theorem residue_right_infCompact {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) :
    ∀ g, ∀ k ∈ infCompact P, C.theta (g * k) = C.theta g := by
  let den (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2
  have hden_eq (g : Matrix (Fin 2) (Fin 2) ℂ) :
      den g = ((g * star g) 1 1).re := by
    dsimp [den]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq]
  have hdet_star (g : Matrix (Fin 2) (Fin 2) ℂ) :
      Matrix.det (star g) = star (Matrix.det g) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
  have hdet_norm (k : GL (Fin 2) ℂ)
      (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
      ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
    have hk' : (k : Matrix (Fin 2) (Fin 2) ℂ) *
        star (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := Matrix.mem_unitaryGroup_iff.mp hk
    have hdet : Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ) *
        star (Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
      calc
        _ = Matrix.det ((k : Matrix (Fin 2) (Fin 2) ℂ) *
            star (k : Matrix (Fin 2) (Fin 2) ℂ)) := by rw [Matrix.det_mul, hdet_star]
        _ = 1 := by rw [hk']; simp
    have hnorm : ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 = 1 := by
      have h := congrArg (fun z : ℂ => ‖z‖) hdet
      simpa only [norm_mul, norm_star, norm_one, sq] using h
    have hnonneg : 0 ≤ ‖Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ)‖ := norm_nonneg _
    nlinarith
  have hspherical (s : ℂ) (g k : GL (Fin 2) ℂ)
      (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
      sphericalC s (g * k) = sphericalC s g := by
    have hk' : (k : Matrix (Fin 2) (Fin 2) ℂ) *
        star (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := Matrix.mem_unitaryGroup_iff.mp hk
    have hden : den ((g : Matrix (Fin 2) (Fin 2) ℂ) *
        (k : Matrix (Fin 2) (Fin 2) ℂ)) = den (g : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hden_eq, hden_eq]
      change ((((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ)) *
        star ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ))) 1 1).re = _
      rw [Matrix.star_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc (k : Matrix (Fin 2) (Fin 2) ℂ)
          (star (k : Matrix (Fin 2) (Fin 2) ℂ)) (star (g : Matrix (Fin 2) (Fin 2) ℂ)), hk']
      simp
    have hratio :
        ‖Matrix.det ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ))‖ /
          den ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ)) =
        ‖Matrix.det (g : Matrix (Fin 2) (Fin 2) ℂ)‖ / den (g : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [Matrix.det_mul, Complex.norm_mul, hdet_norm k hk, mul_one, hden]
    simpa [sphericalC, den] using congrArg (fun x : ℝ => (x : ℂ) ^ (1 + 2 * s)) hratio
  intro g k hk
  apply residue_right_of_scalar_invariant Fam C k ?_ g
  intro s h
  rcases hk with ⟨xk, hqk, hfk, hck⟩
  obtain ⟨xh, hqh⟩ := P.q_surj h
  have hfin : (∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v (xh * xk)))) =
      ∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v xh)) := by
    apply finprod_congr
    intro v
    rw [(P.compF v).map_mul, hfk v, mul_one]
  have harch : (∏ w, (Fam.sec s).fC w (P.compC w (xh * xk))) =
      ∏ w, (Fam.sec s).fC w (P.compC w xh) := by
    apply Finset.prod_congr rfl
    intro w hw
    rw [(P.compC w).map_mul, Fam.fC_sph]
    rcases hck w with ⟨kw, hkw, hcomp⟩
    rw [hcomp]
    let gw : GL (Fin 2) ℂ := Quotient.out (P.compC w xh)
    have hgw : QuotientGroup.mk gw = P.compC w xh := Quotient.out_eq _
    have hqmul : P.compC w xh * QuotientGroup.mk kw = QuotientGroup.mk (gw * kw) := by
      rw [← hgw]
      simp
    rw [hqmul, sphC_mk, hspherical s gw kw hkw, ← hgw, sphC_mk]
  calc
    scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC (P.q (xh * xk)) := by
          rw [P.q.map_mul, hqh, hqk]
    _ = (∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v (xh * xk)))) *
          ∏ w, (Fam.sec s).fC w (P.compC w (xh * xk)) :=
        (scalarOf_q P G (Fam.sec s) (xh * xk)).2
    _ = (∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v xh))) *
          ∏ w, (Fam.sec s).fC w (P.compC w xh) := by rw [hfin, harch]
    _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (P.q xh) :=
        ((scalarOf_q P G (Fam.sec s) xh).2).symm
    _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by rw [hqh]

end ArtinPrimitiveRoots.A1.Theta
