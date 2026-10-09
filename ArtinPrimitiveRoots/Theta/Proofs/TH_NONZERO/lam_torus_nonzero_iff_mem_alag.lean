import ArtinPrimitiveRoots.Theta.Eis

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- A normalized Weyl section with a separating value at one has torus
support exactly on the Lagrangian subgroup. -/
theorem lam_torus_nonzero_iff_mem_alag {P : CoverPackage D S H A}
    (G : GlobalDatum P) (v : FinPlace F) (s : ℂ)
    (f : (P.loc v).L → (G.T v).V)
    (hf : IsSection (P.loc v) (G.T v).weyl s f)
    (h1 : G.lam v (f 1) = 1)
    (hzero : ∀ y : (v.adicCompletion F)ˣ, y ∉ G.Alag v →
      G.lam v ((G.T v).σa y (f 1)) = 0)
    (y : (v.adicCompletion F)ˣ) :
    G.lam v (f ((P.loc v).a y)) ≠ 0 ↔ y ∈ G.Alag v := by
  have heval : G.lam v (f ((P.loc v).a y)) =
      (absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s) *
        G.lam v ((G.T v).σa y⁻¹ (f 1)) := by
    have h := congrArg (G.lam v) (hf.1 0 y 1)
    simp only [ofAdd_zero, map_one, one_mul, mul_one] at h
    change G.lam v (f ((P.loc v).a y)) =
      G.lam v (((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
        (G.T v).σa y⁻¹ (f 1)) at h
    simpa only [map_smul, smul_eq_mul] using h
  have hbase : (absFin v y : ℂ) ≠ 0 := by
    exact_mod_cast (absFin_pos y.ne_zero).ne'
  have hpower : (absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  constructor
  · intro hn
    by_contra hy
    have hyinv : y⁻¹ ∉ G.Alag v := by
      intro hi
      apply hy
      simpa only [inv_inv] using (G.Alag v).inv_mem hi
    exact hn (by rw [heval, hzero y⁻¹ hyinv, mul_zero])
  · intro hy
    have hnonzero : G.lam v ((G.T v).σa y⁻¹ (f 1)) ≠ 0 := by
      have h := congrArg (fun a : (G.T v).V →ₗ[ℂ] (G.T v).V => G.lam v (a (f 1)))
        ((G.T v).σa_mul y y⁻¹)
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
        mul_inv_cancel, (G.T v).σa_one, LinearMap.id_apply, smul_eq_mul, h1] at h
      rw [G.lam_equiv v y hy] at h
      intro hz
      apply (muThree D (H.hilb v y y⁻¹) : ℂˣ).ne_zero
      simpa [hz] using h.symm
    rw [heval]
    exact mul_ne_zero hpower hnonzero

end ArtinPrimitiveRoots.A1.Theta
