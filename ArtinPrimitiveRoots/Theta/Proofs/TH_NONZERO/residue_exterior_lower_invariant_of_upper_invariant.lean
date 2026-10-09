import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_automorphic

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Rational Weyl conjugation transfers upper-root invariance of the residue
to the opposite root subgroup. -/
theorem residue_exterior_lower_invariant_of_upper_invariant
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) (v : FinPlace F) (_hv : v ∉ S.Sf)
    (hupper : ∀ (x : v.adicCompletion F) (g : P.tc.G),
      C.theta (P.emb v ((P.loc v).n (Multiplicative.ofAdd x)) * g) = C.theta g) :
    ∀ (x : v.adicCompletion F) (g : P.tc.G),
      C.theta (P.emb v ((P.loc v).nbar (Multiplicative.ofAdd x)) * g) = C.theta g := by
  let rW := P.ratRP (weylM F)
  have hWF (w : FinPlace F) : P.compF w rW = (P.loc w).w := by
    have hmap : Matrix.GeneralLinearGroup.map
        (algebraMap F (w.adicCompletion F)) (weylM F) =
          weylM (w.adicCompletion F) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [weylM]
    rw [P.compF_ratRP, hmap, ← (P.loc w).sec_w]
  have hWC (w : InfinitePlace F) : P.compC w rW =
      (QuotientGroup.mk (weylM ℂ) : PGL2 ℂ) := by
    have hmap : Matrix.GeneralLinearGroup.map w.embedding (weylM F) = weylM ℂ := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [weylM]
    rw [P.compC_ratRP, hmap]
  have hWsqC : weylM ℂ * weylM ℂ = 1 := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [weylM, Matrix.mul_apply, Fin.sum_univ_two]
  intro x g
  have hconj : rW * P.incl v ((P.loc v).n (Multiplicative.ofAdd x)) * rW =
      P.incl v ((P.loc v).nbar (Multiplicative.ofAdd x)) := by
    apply P.comp_ext
    · intro w
      simp only [map_mul, hWF]
      by_cases hw : v = w
      · subst w
        rw [P.incl_compF, P.incl_compF, (P.loc v).w_n_w]
      · rw [P.incl_compF_other v w hw, P.incl_compF_other v w hw,
          mul_one, (P.loc w).w_sq]
    · intro w
      simp only [map_mul, hWC, P.incl_compC, mul_one]
      rw [← QuotientGroup.mk_mul, hWsqC]
      rfl
  have hq : P.tc.rat (weylM F) * P.emb v ((P.loc v).n (Multiplicative.ofAdd x)) *
      P.tc.rat (weylM F) = P.emb v ((P.loc v).nbar (Multiplicative.ofAdd x)) := by
    simpa only [map_mul, rW, P.q_ratRP, P.q_incl] using congrArg P.q hconj
  calc
    C.theta (P.emb v ((P.loc v).nbar (Multiplicative.ofAdd x)) * g) =
        C.theta (P.tc.rat (weylM F) *
          (P.emb v ((P.loc v).n (Multiplicative.ofAdd x)) *
            (P.tc.rat (weylM F) * g))) := by rw [← hq, mul_assoc, mul_assoc]
    _ = C.theta (P.emb v ((P.loc v).n (Multiplicative.ofAdd x)) *
        (P.tc.rat (weylM F) * g)) := residue_automorphic Fam C _ _
    _ = C.theta (P.tc.rat (weylM F) * g) := hupper _ _
    _ = C.theta g := residue_automorphic Fam C _ _

end ArtinPrimitiveRoots.A1.Theta
