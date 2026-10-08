import ArtinPrimitiveRoots.A2.Interface

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

theorem exterior_cube_generator {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (bc : BalancedChoices D S H Bd)
    (E : ExteriorArithmetic D S H Bd bc)
    (c : S.SqfExtIdeal) (n : S.ExtIdeal) :
    S.IsGen ((bc.gen (E.ofSqf c) * bc.gen n ^ (3 : ℕ) : Fˣ) : F)
      (E.mul (E.ofSqf c) (E.pow n 3)).1 ∧
    Bd.Allowed (bc.gen (E.ofSqf c) * bc.gen n ^ (3 : ℕ)) := by
  have hSpan (a : Fˣ) (m : ℕ) :
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((a ^ m : Fˣ) : F) =
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
          ih, pow_succ]
  have hC := (bc.gen_spec (E.ofSqf c)).1
  have hN := (bc.gen_spec n).1
  have hPow : S.IsGen ((bc.gen n ^ (3 : ℕ) : Fˣ) : F) (E.pow n 3).1 := by
    refine ⟨(E.pow n 3).property, (bc.gen n ^ (3 : ℕ)).ne_zero, ?_⟩
    intro v hv
    rw [hSpan, FractionalIdeal.count_pow, hN.2.2 v hv,
      E.pow_val, FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow]
  constructor
  · refine ⟨(E.mul (E.ofSqf c) (E.pow n 3)).property,
      (bc.gen (E.ofSqf c) * bc.gen n ^ (3 : ℕ)).ne_zero, ?_⟩
    intro v hv
    have hC0 : ((E.ofSqf c).1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr
        (by simpa only [Ideal.zero_eq_bot] using (E.ofSqf c).property.1)
    have hPow0 : ((E.pow n 3).1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr
        (by simpa only [Ideal.zero_eq_bot] using (E.pow n 3).property.1)
    rw [Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul F v
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (bc.gen (E.ofSqf c)).ne_zero)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (bc.gen n ^ (3 : ℕ)).ne_zero),
      hC.2.2 v hv, hPow.2.2 v hv, E.mul_val, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul F v hC0 hPow0]
  · change (QuotientGroup.mk (S.diagU
      (bc.gen (E.ofSqf c) * bc.gen n ^ (3 : ℕ))) : S.V) ∈ Bd.B
    rw [map_mul, map_pow, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
    exact Bd.B.mul_mem (bc.gen_spec (E.ofSqf c)).2
      (Bd.B.pow_mem (bc.gen_spec n).2 3)

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
