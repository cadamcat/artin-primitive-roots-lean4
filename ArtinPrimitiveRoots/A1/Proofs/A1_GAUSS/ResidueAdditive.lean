import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.ResidueCharacter

/-! Additive characters on the residue quotient used in the A1 Gauss sums. -/

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_gauss_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem residue_additive_character_exists (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (P : FinPlace F) (hP : S.IsExterior P.asIdeal)
    (c : F) (hc : S.IsGen c P.asIdeal) :
    ∃ ψ : AddChar (𝓞 F ⧸ P.asIdeal) ℂ,
      (∀ x : 𝓞 F, ψ (Ideal.Quotient.mk P.asIdeal x) =
        S.e A (S.diag (algebraMap (𝓞 F) F x / c))) ∧ ψ.IsPrimitive := by
  classical
  have hC (z t : ℂ) : psiC (z + t) = psiC z * psiC t := by
    simp only [psiC, Complex.add_re, Complex.ofReal_add]
    rw [← Complex.exp_add]
    congr 1
    ring
  let E : AddChar S.FS ℂ :=
    { toFun := S.e A
      map_zero_eq_one' := by simp [SData.e, psiC]
      map_add_eq_mul' := by
        intro x y
        change ((∏ v : S.Sf, A.ψ v.1 (x.1 v + y.1 v)) *
          ∏ w : InfinitePlace F, psiC (x.2 w + y.2 w)) = S.e A x * S.e A y
        simp only [SData.e, AddChar.map_add_eq_mul, hC, Finset.prod_mul_distrib]
        ring }
  let ι := algebraMap (𝓞 F) F
  let f : AddChar (𝓞 F) ℂ :=
    { toFun := fun x => E (S.diag (ι x / c))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro x y
        rw [map_add, add_div, map_add, E.map_add_eq_mul] }
  have hpair := SData.e_pairing_perfect D S A P.asIdeal hP c hc
  let q := Ideal.Quotient.mk P.asIdeal
  have hcongr (x y : 𝓞 F) (hxy : q x = q y) : f x = f y := by
    have hmem : x - y ∈ P.asIdeal :=
      Ideal.Quotient.eq.mp hxy
    have htriv : f (x - y) = 1 := by
      change S.e A (S.diag (ι (x - y) / c)) = 1
      simpa only [mul_one] using hpair.1 (x - y) hmem 1
    simpa only [sub_add_cancel, htriv, one_mul] using f.map_add_eq_mul (x - y) y
  let g : (𝓞 F ⧸ P.asIdeal) → ℂ := fun x => f x.out
  have hout (x : 𝓞 F) : g (q x) = f x := by
    apply hcongr
    exact Ideal.Quotient.mk_out (q x)
  have hg0 : g 0 = 1 := by
    calc
      g 0 = g (q 0) := by rw [map_zero]
      _ = f 0 := hout 0
      _ = 1 := f.map_zero_eq_one
  have hgadd (x y : 𝓞 F ⧸ P.asIdeal) : g (x + y) = g x * g y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) y
    rw [← map_add, hout, hout, hout]
    exact f.map_add_eq_mul a b
  let ψ : AddChar (𝓞 F ⧸ P.asIdeal) ℂ :=
    { toFun := g
      map_zero_eq_one' := hg0
      map_add_eq_mul' := hgadd }
  refine ⟨ψ, hout, ?_⟩
  intro a ha hshift
  have hmem : a.out ∈ P.asIdeal := by
    apply hpair.2 a.out
    intro d
    have hvalue := congrArg (fun θ : AddChar (𝓞 F ⧸ P.asIdeal) ℂ => θ (q d)) hshift
    change ψ (a * q d) = 1 at hvalue
    rw [← Ideal.Quotient.mk_out a, ← map_mul] at hvalue
    change g (q (a.out * d)) = 1 at hvalue
    rw [hout] at hvalue
    exact hvalue
  have hz : q a.out = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact ha ((Ideal.Quotient.mk_out a).symm.trans hz)

end ArtinPrimitiveRoots.Proofs.a1_gauss_sol
