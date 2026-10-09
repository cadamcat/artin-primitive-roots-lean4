import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.FiniteField
import ArtinPrimitiveRoots.Arith.DavenportHasse

/-! Cubic power residue symbols under finite-field norms. -/

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_gauss_sol

theorem cubic_power_residue_norm {k K : Type*} [Field k] [Field K]
    [Algebra k K] [Finite K] (h3 : 3 ∣ Nat.card k - 1) (x : K) :
    algebraMap k K (Algebra.norm k x ^ ((Nat.card k - 1) / 3)) =
      x ^ ((Nat.card K - 1) / 3) := by
  have hdiv : Nat.card k - 1 ∣ Nat.card K - 1 := by
    rw [Module.natCard_eq_pow_finrank (K := k) (V := K)]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  have hexp : ((Nat.card K - 1) / (Nat.card k - 1)) *
      ((Nat.card k - 1) / 3) = (Nat.card K - 1) / 3 := by
    rw [← Nat.mul_div_assoc _ h3, Nat.div_mul_cancel hdiv]
  rw [map_pow, FiniteField.algebraMap_norm_eq_pow, ← pow_mul, hexp]

theorem cubic_character_norm_transport {k K : Type*} [Field k] [Field K]
    [Algebra k K] [Finite K] (h3 : 3 ∣ Nat.card k - 1)
    (α : MulChar k ℂ) (β : MulChar K ℂ) (readRoot : K → ℂ)
    (hα : ∀ u : kˣ, α (u : k) =
      readRoot (algebraMap k K ((u : k) ^ ((Nat.card k - 1) / 3))))
    (hβ : ∀ u : Kˣ, β (u : K) =
      readRoot ((u : K) ^ ((Nat.card K - 1) / 3))) :
    β = ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α := by
  apply MulChar.ext
  intro u
  have hαnorm : α (Algebra.norm k (u : K)) =
      readRoot (algebraMap k K
        (Algebra.norm k (u : K) ^ ((Nat.card k - 1) / 3))) := by
    simpa only [Units.coe_map] using hα (Units.map (Algebra.norm k) u)
  rw [hβ u, ArtinPrimitiveRoots.Arith.normLift_apply, hαnorm,
    cubic_power_residue_norm h3 (u : K)]

theorem normalized_cubic_jacobi_norm_lift {k K : Type*}
    [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]
    (α : MulChar k ℂ) (hα : α ≠ 1) (hα3 : α ^ 3 = 1) :
    let J : ℂ := ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * jacobiSum α α
    ((Fintype.card K : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
      jacobiSum (ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α)
        (ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α) =
      -((-J) ^ Module.finrank k K) := by
  let n := Module.finrank k K
  let c : ℂ := ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)
  let J₀ := jacobiSum α α
  have hαα : α * α ≠ 1 := by
    intro h
    apply hα
    calc
      α = (α * α) * α := by rw [h, one_mul]
      _ = 1 := by simpa only [pow_succ, pow_zero, one_mul] using hα3
  have hn : 1 ≤ n := Module.finrank_pos
  have hcard : Fintype.card K = Fintype.card k ^ n := Module.card_eq_pow_finrank
  have hpos : 0 < (Fintype.card k : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card k)
  have hscale : (Fintype.card K : ℝ) ^ (-(1 / 2 : ℝ)) =
      ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
    rw [hcard, Nat.cast_pow]
    calc
      ((Fintype.card k : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) =
          (Fintype.card k : ℝ) ^ ((n : ℝ) * (-(1 / 2 : ℝ))) :=
        (Real.rpow_natCast_mul (le_of_lt hpos) n (-(1 / 2 : ℝ))).symm
      _ = (Fintype.card k : ℝ) ^ ((-(1 / 2 : ℝ)) * (n : ℝ)) := by
        congr 1
        ring
      _ = ((Fintype.card k : ℝ) ^ (-(1 / 2 : ℝ))) ^ n :=
        Real.rpow_mul_natCast (le_of_lt hpos) (-(1 / 2 : ℝ)) n
  have hc : (((Fintype.card K : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = c ^ n := by
    dsimp [c]
    exact_mod_cast hscale
  have hsign : (-1 : ℂ) ^ (n - 1) = -((-1 : ℂ) ^ n) := by
    have hexp : n = (n - 1) + 1 := by omega
    conv_rhs => rw [hexp, pow_succ]
    ring
  change (((Fintype.card K : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      jacobiSum (ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α)
        (ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α) =
      -((-(c * J₀)) ^ n)
  rw [ArtinPrimitiveRoots.Arith.jacobiSum_lift α α hα hα hαα hn, hc]
  change c ^ n * ((-1 : ℂ) ^ (n - 1) * J₀ ^ n) = -((-(c * J₀)) ^ n)
  rw [hsign, neg_pow (c * J₀) n, mul_pow]
  ring

theorem cubic_character_descends_norm {k K : Type*}
    [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K]
    (h3 : 3 ∣ Nat.card k - 1) (β : MulChar K ℂ)
    (hβ : β ≠ 1) (hβ3 : β ^ 3 = 1) (readRoot : K → ℂ)
    (hread : ∀ u : Kˣ, β (u : K) =
      readRoot ((u : K) ^ ((Nat.card K - 1) / 3))) :
    ∃ α : MulChar k ℂ, α ≠ 1 ∧ α ^ 3 = 1 ∧
      (∀ u : kˣ, α (u : k) =
        readRoot (algebraMap k K ((u : k) ^ ((Nat.card k - 1) / 3)))) ∧
      β = ArtinPrimitiveRoots.Arith.normLift (k := k) (K := K) α := by
  classical
  let g : Kˣ →* kˣ := Units.map (Algebra.norm k)
  have hgsurj : Function.Surjective g := FiniteField.unitsMap_norm_surjective k K
  have hfactor : (β.toUnitHom : Kˣ → ℂˣ).FactorsThrough g := by
    intro u v huv
    apply Units.ext
    rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom, hread u, hread v]
    have hnorm : Algebra.norm k (u : K) = Algebra.norm k (v : K) := by
      simpa only [g, Units.coe_map] using congrArg (fun x : kˣ => (x : k)) huv
    congr 1
    rw [← cubic_power_residue_norm h3 (u : K),
      ← cubic_power_residue_norm h3 (v : K), hnorm]
  let f : kˣ → ℂˣ := Function.extend g β.toUnitHom (fun _ => 1)
  have hf (u : Kˣ) : f (g u) = β.toUnitHom u :=
    hfactor.extend_apply (fun _ => 1) u
  let a : kˣ →* ℂˣ :=
    { toFun := f
      map_one' := by
        calc
          f 1 = f (g 1) := by rw [map_one]
          _ = β.toUnitHom 1 := hf 1
          _ = 1 := map_one _
      map_mul' := by
        intro u v
        obtain ⟨x, rfl⟩ := hgsurj u
        obtain ⟨y, rfl⟩ := hgsurj v
        calc
          f (g x * g y) = f (g (x * y)) := by rw [map_mul]
          _ = β.toUnitHom (x * y) := hf (x * y)
          _ = β.toUnitHom x * β.toUnitHom y := map_mul _ _ _
          _ = f (g x) * f (g y) := by rw [hf, hf] }
  let α : MulChar k ℂ := MulChar.ofUnitHom a
  have hval (u : Kˣ) : α (g u : k) = β (u : K) := by
    change MulChar.ofUnitHom a (g u : k) = β (u : K)
    rw [MulChar.ofUnitHom_coe]
    change ((f (g u) : ℂˣ) : ℂ) = β (u : K)
    rw [hf, MulChar.coe_toUnitHom]
  have hα : α ≠ 1 := by
    intro h
    apply hβ
    apply MulChar.ext
    intro u
    simpa only [h, MulChar.one_apply_coe] using (hval u).symm
  have hα3 : α ^ 3 = 1 := by
    apply MulChar.ext
    intro u
    obtain ⟨x, hx⟩ := hgsurj u
    have hxval : α (u : k) = β (x : K) := by
      rw [← hx]
      exact hval x
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hxval]
    have hβx := congrArg (fun χ : MulChar K ℂ => χ (x : K)) hβ3
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe] using hβx
  have hαread (u : kˣ) : α (u : k) =
      readRoot (algebraMap k K ((u : k) ^ ((Nat.card k - 1) / 3))) := by
    obtain ⟨x, hx⟩ := hgsurj u
    have hxnorm : Algebra.norm k (x : K) = (u : k) := by
      simpa only [g, Units.coe_map] using congrArg (fun y : kˣ => (y : k)) hx
    calc
      α (u : k) = β (x : K) := by rw [← hx]; exact hval x
      _ = readRoot ((x : K) ^ ((Nat.card K - 1) / 3)) := hread x
      _ = readRoot (algebraMap k K
          (Algebra.norm k (x : K) ^ ((Nat.card k - 1) / 3))) :=
        congrArg readRoot (cubic_power_residue_norm h3 (x : K)).symm
      _ = readRoot (algebraMap k K ((u : k) ^ ((Nat.card k - 1) / 3))) := by rw [hxnorm]
  exact ⟨α, hα, hα3, hαread,
    cubic_character_norm_transport h3 α β readRoot hαread hread⟩

end ArtinPrimitiveRoots.Proofs.a1_gauss_sol
