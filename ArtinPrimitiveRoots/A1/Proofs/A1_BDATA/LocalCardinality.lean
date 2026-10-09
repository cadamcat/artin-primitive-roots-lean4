import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.NativeLocalIndex

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The literal sixth-power quotient count is the product of the native local class counts. -/
theorem native_V_class_count_product (D : FieldData F) (S : SData F CE condη) :
    Nat.card S.V = 36 ^ S.Sf.card *
      ∏ v : S.Sf, nativeResidueCharacteristic v.1 ^
        (nativeCompletionDegree v.1 * padicValNat (nativeResidueCharacteristic v.1) 6) := by
  classical
  let Q (v : S.Sf) := (v.1.adicCompletion F)ˣ ⧸
    (powMonoidHom 6 : (v.1.adicCompletion F)ˣ →* (v.1.adicCompletion F)ˣ).range
  let P := (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range
  let φ : S.FSˣ →* (∀ v : S.Sf, Q v) :=
    MonoidHom.pi fun v =>
      (QuotientGroup.mk'
        (powMonoidHom 6 : (v.1.adicCompletion F)ˣ →* (v.1.adicCompletion F)ˣ).range).comp
        (S.compU v)
  have hsurj : Function.Surjective φ := by
    intro q
    let z : S.FSˣ :=
      { val := (fun v => ((Quotient.out (q v) : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F),
          fun _ => 1)
        inv := (fun v => (((Quotient.out (q v) : (v.1.adicCompletion F)ˣ)⁻¹) : v.1.adicCompletion F),
          fun _ => 1)
        val_inv := by ext v <;> simp
        inv_val := by ext v <;> simp }
    refine ⟨z, ?_⟩
    funext v
    have hz : S.compU v z = Quotient.out (q v) := by
      apply Units.ext
      rfl
    change (QuotientGroup.mk (S.compU v z) : Q v) = q v
    rw [hz]
    exact Quotient.out_eq (q v)
  have hker : P = φ.ker := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      apply MonoidHom.mem_ker.mpr
      funext v
      change (QuotientGroup.mk (S.compU v (y ^ 6)) : Q v) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨S.compU v y, ?_⟩
      change (S.compU v y) ^ 6 = S.compU v (y ^ 6)
      exact (map_pow (S.compU v) y 6).symm
    · intro hx
      have hφ : φ x = 1 := hx
      have hfin (v : S.Sf) :
          ∃ c : (v.1.adicCompletion F)ˣ, S.compU v x = c ^ 6 := by
        have hv : (QuotientGroup.mk (S.compU v x) : Q v) = 1 := congrFun hφ v
        obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).mp hv
        exact ⟨c, hc.symm⟩
      have hcomplex (w : InfinitePlace F) : ∃ c : ℂˣ, S.compC w x = c ^ 6 := by
        obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (S.compC w x : ℂ)
          (by norm_num : 0 < (6 : ℕ))
        have hz0 : z ≠ 0 := by
          intro h
          rw [h, zero_pow (by norm_num)] at hz
          exact (S.compC w x).ne_zero hz.symm
        refine ⟨Units.mk0 z hz0, ?_⟩
        apply Units.ext
        exact hz.symm
      choose c hc using hfin
      choose d hd using hcomplex
      let y : S.FSˣ :=
        { val := (fun v => (c v : v.1.adicCompletion F), fun w => (d w : ℂ))
          inv := (fun v => ((c v)⁻¹ : v.1.adicCompletion F), fun w => ((d w)⁻¹ : ℂ))
          val_inv := by ext v <;> simp
          inv_val := by ext v <;> simp }
      refine ⟨y, ?_⟩
      apply Units.ext
      apply Prod.ext <;> funext v
      · exact congrArg Units.val (hc v).symm
      · exact congrArg Units.val (hd v).symm
  let e := QuotientGroup.liftEquiv (H := ∀ v : S.Sf, Q v) (φ := φ) P hsurj hker
  have hcard : Nat.card S.V = ∏ v : S.Sf, Nat.card (Q v) := by
    rw [Nat.card_congr e.toEquiv]
    exact Nat.card_pi
  calc
    Nat.card S.V = ∏ v : S.Sf, Nat.card (Q v) := hcard
    _ = ∏ v : S.Sf, 36 * nativeResidueCharacteristic v.1 ^
        (nativeCompletionDegree v.1 * padicValNat (nativeResidueCharacteristic v.1) 6) := by
      apply Finset.prod_congr rfl
      intro v hv
      exact native_local_sixth_index D v.1
    _ = 36 ^ S.Sf.card * ∏ v : S.Sf, nativeResidueCharacteristic v.1 ^
        (nativeCompletionDegree v.1 * padicValNat (nativeResidueCharacteristic v.1) 6) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
