import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ModulusIdeals
import ArtinPrimitiveRoots.A2.ZeroFree.Results

/-!
# A fixed conductor bound for the quadratic family

The planned bound, in this module's context, is:
```
theorem qs_nq0_quadratic_conductor_bound
    (D : FieldData K) (Sd : SData K CE condη) (H : HilbertData K) :
    ∃ qS : Ideal (𝓞 K), qS ≠ ⊥ ∧
      (∀ v : FinPlace K, qS ≤ v.asIdeal → v ∈ Sd.Sf) ∧
      ∀ (I : Ideal (𝓞 K)) (a : Kˣ), Sd.IsGen (a : K) I →
        ∀ χ : HeckeChar K,
          (∀ v : FinPlace K, χ.loc v = qsNQQuadraticLocal D H v (toLoc v a)) →
          χ.ConductorDvd (I * qS)
```
-/

set_option autoImplicit false

open scoped NumberField WithZero
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {CE : ℕ} {condη : Ideal (𝓞 K)}

/-- A fixed ideal supported on S bounds the S-part of every canonical quadratic conductor. -/
theorem qs_nq0_quadratic_conductor_bound
    (D : FieldData K) (Sd : SData K CE condη) (H : HilbertData K) :
    ∃ qS : Ideal (𝓞 K), qS ≠ ⊥ ∧
      (∀ v : FinPlace K, qS ≤ v.asIdeal → v ∈ Sd.Sf) ∧
      ∀ (I : Ideal (𝓞 K)) (a : Kˣ), Sd.IsGen (a : K) I →
        ∀ χ : HeckeChar K,
          (∀ v : FinPlace K, χ.loc v = qsNQQuadraticLocal D H v (toLoc v a)) →
          χ.ConductorDvd (I * qS) := by
  classical
  obtain ⟨m, hm, _, hsix⟩ := qs_nq0_sixth_power_ray_modulus Sd.Sf
  let qS := qsNQModulusIdeal m.finitePart
  obtain ⟨hqS, he⟩ := qs_nq0_modulus_ideal_exponents m.finitePart
  refine ⟨qS, hqS, ?_, ?_⟩
  · intro v hv
    rw [← hm]
    exact (he v).2.mp hv
  · intro I a ha χ hloc v u hu hui hubound
    have hI : I ≠ 0 := ha.1.1
    have hexp (v : FinPlace K) :
        idealExp v (I * qS) = idealExp v I + m.finitePart v := by
      have hcount := FractionalIdeal.count_mul K v
        (FractionalIdeal.coeIdeal_ne_zero.mpr hI :
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hqS :
          (qS : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0)
      rw [← FractionalIdeal.coeIdeal_mul I qS,
        FractionalIdeal.count_coe K v (mul_ne_zero hI hqS),
        FractionalIdeal.count_coe K v hI, FractionalIdeal.count_coe K v hqS] at hcount
      change (idealExp v (I * qS) : ℤ) =
        (idealExp v I : ℤ) + (idealExp v qS : ℤ) at hcount
      rw [(he v).1] at hcount
      exact_mod_cast hcount
    rw [hloc v]
    by_cases hv : v ∈ Sd.Sf
    · have hle : WithZero.exp (-(idealExp v (I * qS) : ℤ)) ≤
          WithZero.exp (-(m.finitePart v : ℤ)) := by
        apply WithZero.exp_le_exp.mpr
        rw [hexp]
        omega
      obtain ⟨b, rfl⟩ := hsix v hv u (hubound.trans hle)
      rw [map_pow]
      have h2 := congrArg (fun f : (v.adicCompletion K)ˣ →* ℂˣ => f b)
        (qs_nq0_quadratic_local_square D H v (toLoc v a))
      change qsNQQuadraticLocal D H v (toLoc v a) b ^ 2 = 1 at h2
      calc
        qsNQQuadraticLocal D H v (toLoc v a) b ^ 6 =
            (qsNQQuadraticLocal D H v (toLoc v a) b ^ 2) ^ 3 := by
          rw [← pow_mul]
        _ = 1 := by rw [h2, one_pow]
    · have h6 : (6 : 𝓞 K) ∉ v.asIdeal := fun h => hv (Sd.over6 v h)
      have hmv : m.finitePart v = 0 :=
        Finsupp.notMem_support_iff.mp (by rwa [hm])
      by_cases heI : idealExp v I = 0
      · have hcount : FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = 0 := by
          rw [ha.2.2 v hv, FractionalIdeal.count_coe K v hI]
          change (idealExp v I : ℤ) = 0
          rw [heI, Int.natCast_zero]
        have hlog := qs_nq0_count_spanSingleton_eq_neg_log_valuation v (a : K) a.ne_zero
        rw [hcount] at hlog
        have hz : WithZero.log (v.valuation K (a : K)) = 0 := neg_eq_zero.mp hlog.symm
        have hva : v.valuation K (a : K) = 1 := by
          calc
            v.valuation K (a : K) = WithZero.exp (WithZero.log (v.valuation K (a : K))) :=
              (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr a.ne_zero)).symm
            _ = 1 := by rw [hz, WithZero.exp_zero]
        exact qs_nq0_quadratic_local_unit_trivial D H v h6 a hva u ⟨hu, hui⟩
      · have hpos : 0 < idealExp v (I * qS) := by
          rw [hexp, hmv]
          omega
        have hlt : WithZero.exp (-(idealExp v (I * qS) : ℤ)) < 1 := by
          calc
            WithZero.exp (-(idealExp v (I * qS) : ℤ)) < WithZero.exp (0 : ℤ) :=
              WithZero.exp_lt_exp.mpr (by omega)
            _ = 1 := WithZero.exp_zero
        exact qs_nq0_quadratic_local_principal_unit_trivial D H v h6 a u
          (lt_of_le_of_lt hubound hlt)

/-!
The primitive-conductor selection step has this exact signature:
```
theorem qs_nq0_primitive_conductor_exists (χ : HeckeChar K)
    (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) (hbound : χ.ConductorDvd q) :
    ∃ f : Ideal (𝓞 K), IsPrimitiveConductor χ f ∧
      Ideal.absNorm f ≤ Ideal.absNorm q
```
-/

/-- Every nonzero conductor bound supplies a primitive conductor of no greater norm. -/
theorem qs_nq0_primitive_conductor_exists (χ : HeckeChar K)
    (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) (hbound : χ.ConductorDvd q) :
    ∃ f : Ideal (𝓞 K), IsPrimitiveConductor χ f ∧
      Ideal.absNorm f ≤ Ideal.absNorm q := by
  classical
  let P (n : ℕ) := ∃ f : Ideal (𝓞 K),
    f ≠ ⊥ ∧ χ.ConductorDvd f ∧ Ideal.absNorm f = n
  have hp : ∃ n : ℕ, P n := ⟨Ideal.absNorm q, q, hq, hbound, rfl⟩
  obtain ⟨f, hf, hfc, he⟩ := Nat.find_spec hp
  have hmin (g : Ideal (𝓞 K)) (hg : g ≠ ⊥) (hgc : χ.ConductorDvd g) :
      Ideal.absNorm f ≤ Ideal.absNorm g := by
    rw [he]
    exact Nat.find_min' hp ⟨g, hg, hgc, rfl⟩
  exact ⟨f, ⟨hf, hfc, hmin⟩, hmin q hq hbound⟩

/-!
The exponent-supremum step has this exact signature:
```
theorem qs_nq0_idealExp_sup (I J : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (v : FinPlace K) :
    idealExp v (I ⊔ J) = min (idealExp v I) (idealExp v J)
```
-/

/-- The prime exponent of an ideal supremum is the minimum of the two exponents. -/
theorem qs_nq0_idealExp_sup (I J : Ideal (𝓞 K))
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (v : FinPlace K) :
    idealExp v (I ⊔ J) = min (idealExp v I) (idealExp v J) := by
  classical
  have hpow (L : Ideal (𝓞 K)) (hL : L ≠ ⊥) (k : ℕ) :
      k ≤ idealExp v L ↔ L ≤ v.asIdeal ^ k := by
    change k ≤ (Associates.mk v.asIdeal).count (Associates.mk L).factors ↔
      L ≤ v.asIdeal ^ k
    rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hL)
      v.associates_irreducible, ← Associates.mk_pow,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]
  have hsup : I ⊔ J ≠ ⊥ := ne_bot_of_le_ne_bot hI le_sup_left
  have hiff (k : ℕ) :
      k ≤ idealExp v (I ⊔ J) ↔ k ≤ min (idealExp v I) (idealExp v J) := by
    rw [hpow (I ⊔ J) hsup k, sup_le_iff, ← hpow I hI k, ← hpow J hJ k, le_min_iff]
  exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)

/-!
Closure of conductor bounds under supremum has this exact signature:
```
theorem qs_nq0_conductorDvd_sup (χ : HeckeChar K)
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hχI : χ.ConductorDvd I) (hχJ : χ.ConductorDvd J) :
    χ.ConductorDvd (I ⊔ J)
```
-/

/-- A character's nonzero conductor bounds are closed under ideal supremum. -/
theorem qs_nq0_conductorDvd_sup (χ : HeckeChar K)
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hχI : χ.ConductorDvd I) (hχJ : χ.ConductorDvd J) :
    χ.ConductorDvd (I ⊔ J) := by
  intro v u hu hui hubound
  rw [qs_nq0_idealExp_sup I J hI hJ v] at hubound
  rcases le_total (idealExp v I) (idealExp v J) with hle | hle
  · rw [min_eq_left hle] at hubound
    exact hχI v u hu hui hubound
  · rw [min_eq_right hle] at hubound
    exact hχJ v u hu hui hubound

end ArtinPrimitiveRoots.A2
