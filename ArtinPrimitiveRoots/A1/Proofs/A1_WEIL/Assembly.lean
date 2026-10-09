import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.Gamma

/-! Descent of local quadratic indices to the isotropic subgroup `B`. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The algebraic assembly uses actual local indices, with no choice of prime generators. -/
theorem quadratic_sign_character_of_indices
    (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (H : HilbertData F) (Bd : BData S H)
    (w : (v : FinPlace F) → (v.adicCompletion F)ˣ → ℂˣ)
    (hone : ∀ v, w v 1 = 1)
    (hsquare : ∀ v a b, w v (a * b ^ 2) = w v a)
    (hdefect : ∀ v a b, w v a * w v b =
      complexRoot D (H.hilb v a b) ^ 3 * w v (a * b))
    (hproduct : ∀ a : Fˣ, ∏ᶠ v, w v (toLoc v a) = 1)
    (hunit : ∀ v : FinPlace F, v ∉ S.Sf → ∀ a : Fˣ,
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = 0 →
      w v (toLoc v a) = 1)
    (hprime : ∀ v : FinPlace F, v ∉ S.Sf → ∀ p : Fˣ,
      S.IsGen (p : F) v.asIdeal →
      ((w v (toLoc v (p⁻¹)) : ℂˣ) : ℂ) = gamma D S A 3 v.asIdeal (p : F)) :
    ∃ θB : Bd.B →* ℂˣ, ∀ v : FinPlace F, v ∉ S.Sf →
      ∀ p : Fˣ, ∀ (hpgen : S.IsGen (p : F) v.asIdeal),
        ∀ (hpAllowed : Bd.Allowed p),
        gamma D S A 3 v.asIdeal (p : F) =
          ((θB ⟨(QuotientGroup.mk (S.diagU p) : S.V), hpAllowed⟩ : ℂˣ) : ℂ) := by
  classical
  letI : CommGroup S.V := QuotientGroup.Quotient.commGroup _
  let N : Subgroup S.FSˣ := (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
  let q : S.FSˣ →* S.V := QuotientGroup.mk' N
  let sIndex : S.FSˣ → ℂˣ := fun x => ∏ v : S.Sf, w v.1 (S.compU v x)
  have hsix (x y : S.FSˣ) : sIndex (x * y ^ 6) = sIndex x := by
    apply Finset.prod_congr rfl
    intro v hv
    simp only [map_mul, map_pow]
    rw [show S.compU v y ^ 6 = (S.compU v y ^ 3) ^ 2 from pow_mul _ 3 2]
    exact hsquare v.1 (S.compU v x) (S.compU v y ^ 3)
  have hcongr (x y : S.FSˣ) (hxy : q x = q y) : sIndex x = sIndex y := by
    obtain ⟨z, hz, hxz⟩ := (QuotientGroup.mk'_eq_mk' (N := N)).mp hxy
    obtain ⟨u, hu⟩ := hz
    change u ^ 6 = z at hu
    rw [← hxz, ← hu, hsix]
  let qIndex : S.V → ℂˣ := fun x => sIndex x.out
  have hqIndex (x : S.FSˣ) : qIndex (q x) = sIndex x := by
    exact hcongr _ _ (Quotient.out_eq _)
  have hsIndex_one : sIndex 1 = 1 := by
    simp [sIndex, hone]
  have hsIndex_mul (x y : S.FSˣ)
      (hx : (QuotientGroup.mk x : S.V) ∈ Bd.B)
      (hy : (QuotientGroup.mk y : S.V) ∈ Bd.B) :
      sIndex x * sIndex y = sIndex (x * y) := by
    have hH : (∏ v : S.Sf, complexRoot D (H.hilb v.1 (S.compU v x) (S.compU v y))) = 1 := by
      rw [← map_prod, ← SData.HS, Bd.isotropic x y hx hy, map_one]
    calc
      sIndex x * sIndex y =
          ∏ v : S.Sf, w v.1 (S.compU v x) * w v.1 (S.compU v y) := by
            rw [Finset.prod_mul_distrib]
      _ = ∏ v : S.Sf,
          complexRoot D (H.hilb v.1 (S.compU v x) (S.compU v y)) ^ 3 *
            w v.1 (S.compU v (x * y)) := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [hdefect, map_mul]
      _ = (∏ v : S.Sf,
          complexRoot D (H.hilb v.1 (S.compU v x) (S.compU v y))) ^ 3 *
            sIndex (x * y) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow]
      _ = sIndex (x * y) := by rw [hH]; simp
  have hqIndex_mul (x y : S.V) (hx : x ∈ Bd.B) (hy : y ∈ Bd.B) :
      qIndex (x * y) = qIndex x * qIndex y := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N y
    rw [← q.map_mul, hqIndex, hqIndex, hqIndex]
    exact (hsIndex_mul a b hx hy).symm
  let θB : Bd.B →* ℂˣ :=
    { toFun := fun x => qIndex x.1
      map_one' := by
        change qIndex 1 = 1
        rw [← q.map_one, hqIndex, hsIndex_one]
      map_mul' := fun x y => hqIndex_mul x.1 y.1 x.2 y.2 }
  refine ⟨θB, ?_⟩
  intro P hP p hp ha
  let f : FinPlace F → ℂˣ := fun v => w v (toLoc v (p⁻¹))
  have houtside (v : FinPlace F) (hvS : v ∉ S.Sf) (hvP : v ≠ P) : f v = 1 := by
    have hpcount : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 0 := by
      rw [hp.2.2 v hvS]
      exact FractionalIdeal.count_maximal_coprime (K := F) v hvP.symm
    apply hunit v hvS (p⁻¹)
    rw [Units.val_inv_eq_inv_val, ← FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.count_inv, hpcount, neg_zero]
  have hsupp : Function.mulSupport f ⊆ (insert P S.Sf : Finset (FinPlace F)) := by
    intro v hv
    by_contra hnot
    have hvP : v ≠ P := by
      intro heq
      exact hnot (by simp [heq])
    have hvS : v ∉ S.Sf := by
      intro hmem
      exact hnot (Finset.mem_insert_of_mem hmem)
    exact hv (houtside v hvS hvP)
  have hfinprod : (∏ᶠ v, f v) = f P * sIndex (S.diagU (p⁻¹)) := by
    rw [finprod_eq_prod_of_mulSupport_subset f hsupp, Finset.prod_insert hP]
    congr 1
    rw [← Finset.prod_coe_sort]
    rfl
  have hglobal : f P * sIndex (S.diagU (p⁻¹)) = 1 := by
    rw [← hfinprod]
    exact hproduct (p⁻¹)
  have hfP : f P = (sIndex (S.diagU (p⁻¹)))⁻¹ :=
    eq_inv_of_mul_eq_one_left hglobal
  have hθinv : (sIndex (S.diagU (p⁻¹)))⁻¹ =
      θB ⟨(QuotientGroup.mk (S.diagU p) : S.V), ha⟩ := by
    have hbInv : (θB ⟨(QuotientGroup.mk (S.diagU p) : S.V), ha⟩)⁻¹ =
        sIndex (S.diagU (p⁻¹)) := by
      rw [← map_inv]
      change qIndex ((q (S.diagU p))⁻¹) = _
      rw [← q.map_inv, hqIndex, ← S.diagU.map_inv]
    simpa only [inv_inv] using congrArg (fun z : ℂˣ => z⁻¹) hbInv.symm
  calc
    gamma D S A 3 P.asIdeal (p : F) = ((f P : ℂˣ) : ℂ) :=
      (hprime P hP p hp).symm
    _ = (((sIndex (S.diagU (p⁻¹)))⁻¹ : ℂˣ) : ℂ) := congrArg Units.val hfP
    _ = ((θB ⟨(QuotientGroup.mk (S.diagU p) : S.V), ha⟩ : ℂˣ) : ℂ) :=
      congrArg Units.val hθinv

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
