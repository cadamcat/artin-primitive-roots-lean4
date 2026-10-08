import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.EqualClass

/-!
# Local algebra for product conductors

Cubed Hilbert symbols preserve multiplication and division in their first
argument. These identities compare products of canonical local characters
with the characters of products and quotients of their generators.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- The local quadratic character preserves multiplication and division of its parameter. -/
theorem qs_nq0_quadratic_local_mul_div
    (D : FieldData K) (H : HilbertData K) (v : FinPlace K)
    (a b : (v.adicCompletion K)ˣ) :
    qsNQQuadraticLocal D H v (a * b) =
      qsNQQuadraticLocal D H v a * qsNQQuadraticLocal D H v b ∧
    qsNQQuadraticLocal D H v (a / b) =
      qsNQQuadraticLocal D H v a / qsNQQuadraticLocal D H v b := by
  let g : rootsOfUnity 6 K →* ℂˣ :=
    (powMonoidHom 3 : ℂˣ →* ℂˣ).comp
      ((Units.map D.σ0.toMonoidHom).comp (rootsOfUnity 6 K).subtype)
  let f : (v.adicCompletion K)ˣ →* ((v.adicCompletion K)ˣ →* ℂˣ) :=
    MonoidHom.mk' (fun x => qsNQQuadraticLocal D H v x) (fun x y => by
      apply MonoidHom.ext
      intro u
      change g (H.hilb v (x * y) u) = g (H.hilb v x u) * g (H.hilb v y u)
      rw [H.mul_left, map_mul])
  refine ⟨f.map_mul a b, ?_⟩
  change f (a / b) = f a / f b
  exact map_div f a b


/-- Products of exterior generators generate the product exterior ideal. -/
theorem qs_nq0_generators_mul
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη) (I J : Ideal (𝓞 K)) (a b : Kˣ)
    (ha : Sd.IsGen (a : K) I) (hb : Sd.IsGen (b : K) J) :
    Sd.IsGen ((a * b : Kˣ) : K) (I * J) := by
  refine ⟨⟨mul_ne_zero ha.1.1 hb.1.1, ?_⟩, (a * b).ne_zero, ?_⟩
  · intro v hv hIJ
    obtain hI | hJ := v.isPrime.mul_le.mp hIJ
    · exact ha.1.2 v hv hI
    · exact hb.1.2 v hv hJ
  · intro v hv
    rw [Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K v
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr a.ne_zero)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr b.ne_zero),
      ha.2.2 v hv, hb.2.2 v hv, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul K v
        (FractionalIdeal.coeIdeal_ne_zero.mpr ha.1.1)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hb.1.1)]

/-!
The quotient-character comparison uses these two representations:
```
theorem qs_nq0_quotient_character_local
    (D : FieldData K) (H : HilbertData K) (a b : Kˣ)
    (χa χb : HeckeChar K)
    (hloca : ∀ v : FinPlace K,
      χa.loc v = qsNQQuadraticLocal D H v (toLoc v a))
    (hlocb : ∀ v : FinPlace K,
      χb.loc v = qsNQQuadraticLocal D H v (toLoc v b)) :
    (∀ v : FinPlace K, (χa * χb⁻¹).loc v =
      qsNQQuadraticLocal D H v (toLoc v (a * b))) ∧
    (∀ v : FinPlace K, (χa * χb⁻¹).loc v =
      qsNQQuadraticLocal D H v (toLoc v (a / b)))
```
At S, the quotient representation will use the sixth root of the allowed
ratio. Outside S, the product representation will use the product generator.
-/

/-- The quotient character has both the product and quotient generator as local parameters. -/
theorem qs_nq0_quotient_character_local
    (D : FieldData K) (H : HilbertData K) (a b : Kˣ)
    (χa χb : HeckeChar K)
    (hloca : ∀ v : FinPlace K,
      χa.loc v = qsNQQuadraticLocal D H v (toLoc v a))
    (hlocb : ∀ v : FinPlace K,
      χb.loc v = qsNQQuadraticLocal D H v (toLoc v b)) :
    (∀ v : FinPlace K, (χa * χb⁻¹).loc v =
      qsNQQuadraticLocal D H v (toLoc v (a * b))) ∧
    (∀ v : FinPlace K, (χa * χb⁻¹).loc v =
      qsNQQuadraticLocal D H v (toLoc v (a / b))) := by
  have hquot (v : FinPlace K) : (χa * χb⁻¹).loc v =
      qsNQQuadraticLocal D H v (toLoc v a) /
        qsNQQuadraticLocal D H v (toLoc v b) := by
    apply MonoidHom.ext
    intro u
    change χa.loc v u * (χb.loc v u)⁻¹ =
      qsNQQuadraticLocal D H v (toLoc v a) u /
        qsNQQuadraticLocal D H v (toLoc v b) u
    rw [hloca v, hlocb v, div_eq_mul_inv]
  constructor
  · intro v
    rw [hquot, map_mul, (qs_nq0_quadratic_local_mul_div D H v _ _).1]
    apply MonoidHom.ext
    intro u
    change qsNQQuadraticLocal D H v (toLoc v a) u /
        qsNQQuadraticLocal D H v (toLoc v b) u =
      qsNQQuadraticLocal D H v (toLoc v a) u *
        qsNQQuadraticLocal D H v (toLoc v b) u
    have hsquare := congrArg (fun f : (v.adicCompletion K)ˣ →* ℂˣ => f u)
      (qs_nq0_quadratic_local_square D H v (toLoc v b))
    change qsNQQuadraticLocal D H v (toLoc v b) u ^ 2 = 1 at hsquare
    have hinv : (qsNQQuadraticLocal D H v (toLoc v b) u)⁻¹ =
        qsNQQuadraticLocal D H v (toLoc v b) u :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsquare)
    rw [div_eq_mul_inv, hinv]
  · intro v
    rw [hquot, map_div, (qs_nq0_quadratic_local_mul_div D H v _ _).2]


/-!
The next conductor bound has this exact signature:
```
theorem qs_nq0_quotient_conductor_bound
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (D : FieldData K) (Sd : SData K CE condη) (H : HilbertData K)
    (I J : Ideal (𝓞 K)) (a b : Kˣ)
    (ha : Sd.IsGen (a : K) I) (hb : Sd.IsGen (b : K) J)
    (χa χb : HeckeChar K)
    (hloca : ∀ v : FinPlace K,
      χa.loc v = qsNQQuadraticLocal D H v (toLoc v a))
    (hlocb : ∀ v : FinPlace K,
      χb.loc v = qsNQQuadraticLocal D H v (toLoc v b))
    (hroot : ∃ y : Sd.FSˣ, Sd.diagU (a / b) = y ^ 6) :
    (χa * χb⁻¹).ConductorDvd (I * J)
```
-/

/-- A sixth-power ratio at S removes the S-part of the quotient conductor bound. -/
theorem qs_nq0_quotient_conductor_bound
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (D : FieldData K) (Sd : SData K CE condη) (H : HilbertData K)
    (I J : Ideal (𝓞 K)) (a b : Kˣ)
    (ha : Sd.IsGen (a : K) I) (hb : Sd.IsGen (b : K) J)
    (χa χb : HeckeChar K)
    (hloca : ∀ v : FinPlace K,
      χa.loc v = qsNQQuadraticLocal D H v (toLoc v a))
    (hlocb : ∀ v : FinPlace K,
      χb.loc v = qsNQQuadraticLocal D H v (toLoc v b))
    (hroot : ∃ y : Sd.FSˣ, Sd.diagU (a / b) = y ^ 6) :
    (χa * χb⁻¹).ConductorDvd (I * J) := by
  classical
  obtain ⟨hlocprod, hlocquot⟩ :=
    qs_nq0_quotient_character_local D H a b χa χb hloca hlocb
  have hgen := qs_nq0_generators_mul Sd I J a b ha hb
  intro v u hu hui hubound
  by_cases hv : v ∈ Sd.Sf
  · obtain ⟨y, hy⟩ := hroot
    have hcomp : Sd.compU ⟨v, hv⟩ (Sd.diagU (a / b)) = toLoc v (a / b) := by
      apply Units.ext
      rfl
    have hlocalroot := congrArg (Sd.compU ⟨v, hv⟩) hy
    rw [hcomp, map_pow] at hlocalroot
    rw [hlocquot v]
    change Units.map D.σ0.toMonoidHom
      (H.hilb v (toLoc v (a / b)) u : Kˣ) ^ 3 = 1
    rw [H.sixth_power v _ u ⟨Sd.compU ⟨v, hv⟩ y, hlocalroot⟩]
    simp
  · rw [hlocprod v]
    have h6 : (6 : 𝓞 K) ∉ v.asIdeal := fun h => hv (Sd.over6 v h)
    by_cases heIJ : idealExp v (I * J) = 0
    · have hcount : FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((a * b : Kˣ) : K)) = 0 := by
        rw [hgen.2.2 v hv, FractionalIdeal.count_coe K v hgen.1.1]
        change (idealExp v (I * J) : ℤ) = 0
        rw [heIJ, Int.natCast_zero]
      have hlog := qs_nq0_count_spanSingleton_eq_neg_log_valuation v
        ((a * b : Kˣ) : K) (a * b).ne_zero
      rw [hcount] at hlog
      have hz : WithZero.log (v.valuation K ((a * b : Kˣ) : K)) = 0 :=
        neg_eq_zero.mp hlog.symm
      have hvab : v.valuation K ((a * b : Kˣ) : K) = 1 := by
        calc
          v.valuation K ((a * b : Kˣ) : K) =
              WithZero.exp (WithZero.log (v.valuation K ((a * b : Kˣ) : K))) :=
            (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr (a * b).ne_zero)).symm
          _ = 1 := by rw [hz, WithZero.exp_zero]
      exact qs_nq0_quadratic_local_unit_trivial D H v h6 (a * b) hvab u ⟨hu, hui⟩
    · have hlt : WithZero.exp (-(idealExp v (I * J) : ℤ)) < 1 := by
        calc
          WithZero.exp (-(idealExp v (I * J) : ℤ)) < WithZero.exp (0 : ℤ) :=
            WithZero.exp_lt_exp.mpr (by omega)
          _ = 1 := WithZero.exp_zero
      exact qs_nq0_quadratic_local_principal_unit_trivial D H v h6 (a * b) u
        (lt_of_le_of_lt hubound hlt)

end ArtinPrimitiveRoots.A2
