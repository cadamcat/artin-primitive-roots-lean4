import ArtinPrimitiveRoots.A1.Proofs.A1_BDATA.PrimeComplement

set_option autoImplicit false
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

/-- Combine the prime-exponent isotropic complements of the two primary
components of a finite exponent-six group. -/
theorem exponent_six_complement {F G : Type} [Field F] [CommGroup G] [Finite G]
    (hmu : ∃ ζ : F, IsPrimitiveRoot ζ 6) (hexp : ∀ x : G, x ^ 6 = 1)
    (β : G →* (G →* rootsOfUnity 6 F))
    (ha : ∀ x : G, β x x = 1)
    (hn : ∀ x : G, (∀ y : G, β x y = 1) → x = 1)
    (E : Subgroup G) (N : ℕ)
    (hcard : Nat.card G = 6 ^ (2 * N)) (hEcard : Nat.card E = 6 ^ N)
    (hE : ∀ x ∈ E, ∀ y ∈ E, β x y = 1) :
    ∃ B : Subgroup G, (∀ x ∈ B, ∀ y ∈ B, β x y = 1) ∧ IsCompl E B := by
  classical
  let G2 := (powMonoidHom 2 : G →* G).ker
  let G3 := (powMonoidHom 3 : G →* G).ker
  let π2 : G →* G2 :=
    { toFun := fun x => ⟨x ^ 3, by
        change (x ^ 3) ^ 2 = 1
        simpa only [← pow_mul, Nat.reduceMul] using hexp x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp [mul_pow] }
  let π3 : G →* G3 :=
    { toFun := fun x => ⟨x ^ 4, by
        change (x ^ 4) ^ 3 = 1
        have h12 := congrArg (fun y : G => y ^ (2 : ℕ)) (hexp x)
        simpa only [← pow_mul, Nat.reduceMul, one_pow] using h12⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp [mul_pow] }
  let m : G2 × G3 →* G :=
    { toFun := fun z => (z.1 : G) * (z.2 : G)
      map_one' := by simp
      map_mul' := by
        intro x y
        change ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
          ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
        ac_rfl }
  have h2 (a : G2) : (a : G) ^ 2 = 1 := a.property
  have h3 (b : G3) : (b : G) ^ 3 = 1 := b.property
  have hleft2 (a : G2) (b : G3) : π2 (m (a, b)) = a := by
    apply Subtype.ext
    change ((a : G) * (b : G)) ^ 3 = (a : G)
    rw [mul_pow, pow_succ, h2, h3, one_mul, mul_one]
  have hleft3 (a : G2) (b : G3) : π3 (m (a, b)) = b := by
    apply Subtype.ext
    change ((a : G) * (b : G)) ^ 4 = (b : G)
    rw [mul_pow]
    have ha4 : (a : G) ^ (4 : ℕ) = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, h2, one_pow]
    rw [ha4, pow_succ, h3, one_mul, one_mul]
  have hright (x : G) : m (π2 x, π3 x) = x := by
    change x ^ 3 * x ^ 4 = x
    rw [← pow_add]
    change x ^ 7 = x
    rw [pow_succ, hexp, one_mul]
  let eCRT : G ≃* (G2 × G3) :=
    { toFun := fun x => (π2 x, π3 x)
      invFun := m
      left_inv := hright
      right_inv := fun z => Prod.ext (hleft2 z.1 z.2) (hleft3 z.1 z.2)
      map_mul' := fun x y => Prod.ext (π2.map_mul x y) (π3.map_mul x y) }
  let E2 := E.comap G2.subtype
  let E3 := E.comap G3.subtype
  have hEmap : E.map eCRT.toMonoidHom = E2.prod E3 := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_prod]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨E.pow_mem hx 3, E.pow_mem hx 4⟩
    · intro hy
      refine ⟨eCRT.symm y, ?_, eCRT.apply_symm_apply y⟩
      change (y.1 : G) * (y.2 : G) ∈ E
      exact E.mul_mem hy.1 hy.2
  let eE : E ≃* (E2 × E3) :=
    (eCRT.subgroupMap E).trans
      ((MulEquiv.subgroupCongr hEmap).trans (Subgroup.prodEquiv E2 E3))
  have hcardG : Nat.card G = Nat.card G2 * Nat.card G3 := by
    rw [← Nat.card_prod]
    exact Nat.card_congr eCRT.toEquiv
  have hcardE : Nat.card E = Nat.card E2 * Nat.card E3 := by
    rw [← Nat.card_prod]
    exact Nat.card_congr eE.toEquiv
  letI : Module (ZMod 2) (Additive G2) := AddCommGroup.zmodModule (n := 2) (fun x => by
    apply Additive.toMul.injective
    change Additive.toMul x ^ (2 : ℕ) = 1
    apply Subtype.ext
    exact h2 (Additive.toMul x))
  letI : Module (ZMod 3) (Additive G3) := AddCommGroup.zmodModule (n := 3) (fun x => by
    apply Additive.toMul.injective
    change Additive.toMul x ^ (3 : ℕ) = 1
    apply Subtype.ext
    exact h3 (Additive.toMul x))
  letI : Module (ZMod 2) (Additive E2) := AddCommGroup.zmodModule (n := 2) (fun x => by
    apply Additive.toMul.injective
    change Additive.toMul x ^ (2 : ℕ) = 1
    apply Subtype.ext
    apply Subtype.ext
    exact h2 ((Additive.toMul x : E2) : G2))
  letI : Module (ZMod 3) (Additive E3) := AddCommGroup.zmodModule (n := 3) (fun x => by
    apply Additive.toMul.injective
    change Additive.toMul x ^ (3 : ℕ) = 1
    apply Subtype.ext
    apply Subtype.ext
    exact h3 ((Additive.toMul x : E3) : G3))
  have hcG2 : Nat.card G2 = 2 ^ Module.finrank (ZMod 2) (Additive G2) :=
    (Nat.card_congr (Additive.ofMul : G2 ≃ Additive G2)).trans (by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G2)))
  have hcG3 : Nat.card G3 = 3 ^ Module.finrank (ZMod 3) (Additive G3) :=
    (Nat.card_congr (Additive.ofMul : G3 ≃ Additive G3)).trans (by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive G3)))
  have hcE2 : Nat.card E2 = 2 ^ Module.finrank (ZMod 2) (Additive E2) :=
    (Nat.card_congr (Additive.ofMul : E2 ≃ Additive E2)).trans (by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E2)))
  have hcE3 : Nat.card E3 = 3 ^ Module.finrank (ZMod 3) (Additive E3) :=
    (Nat.card_congr (Additive.ofMul : E3 ≃ Additive E3)).trans (by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive E3)))
  have hsq : Nat.card G = (Nat.card E) ^ 2 := by
    rw [hcard, hEcard, ← pow_mul, Nat.mul_comm]
  have hpow :
      2 ^ Module.finrank (ZMod 2) (Additive G2) *
        3 ^ Module.finrank (ZMod 3) (Additive G3) =
      (2 ^ Module.finrank (ZMod 2) (Additive E2) *
        3 ^ Module.finrank (ZMod 3) (Additive E3)) ^ 2 := by
    rw [← hcG2, ← hcG3, ← hcE2, ← hcE3, ← hcardG, ← hcardE]
    exact hsq
  have hd2 : Module.finrank (ZMod 2) (Additive G2) =
      2 * Module.finrank (ZMod 2) (Additive E2) := by
    have hfac := congrArg (fun n : ℕ => n.factorization 2) hpow
    simpa [Nat.factorization_mul, Nat.factorization_pow,
      Nat.prime_two.factorization, Nat.prime_three.factorization] using hfac
  have hd3 : Module.finrank (ZMod 3) (Additive G3) =
      2 * Module.finrank (ZMod 3) (Additive E3) := by
    have hfac := congrArg (fun n : ℕ => n.factorization 3) hpow
    simpa [Nat.factorization_mul, Nat.factorization_pow,
      Nat.prime_two.factorization, Nat.prime_three.factorization] using hfac
  have hsquare2 : Nat.card G2 = (Nat.card E2) ^ 2 := by
    rw [hcG2, hcE2, hd2, ← pow_mul, Nat.mul_comm]
  have hsquare3 : Nat.card G3 = (Nat.card E3) ^ 2 := by
    rw [hcG3, hcE3, hd3, ← pow_mul, Nat.mul_comm]
  let restricted (p : ℕ) (T : Subgroup G) (hpT : ∀ x : T, (x : G) ^ p = 1) :
      T →* (T →* rootsOfUnity p F) :=
    { toFun := fun x =>
        { toFun := fun y => ⟨(β (x : G) (y : G) : Fˣ), by
            change (β (x : G) (y : G) : Fˣ) ^ p = 1
            have hh := congrArg (fun f : G →* rootsOfUnity 6 F => f (y : G))
              (β.map_pow (x : G) p)
            rw [hpT x, β.map_one] at hh
            change 1 = (β (x : G) (y : G)) ^ p at hh
            exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) hh.symm⟩
          map_one' := by
            apply Subtype.ext
            exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ))
              ((β (x : G)).map_one)
          map_mul' := by
            intro y z
            apply Subtype.ext
            exact congrArg (fun w : rootsOfUnity 6 F => (w : Fˣ))
              ((β (x : G)).map_mul (y : G) (z : G)) }
      map_one' := by
        apply MonoidHom.ext
        intro y
        apply Subtype.ext
        have hh : β 1 (y : G) = 1 := by rw [β.map_one]; rfl
        exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) hh
      map_mul' := by
        intro x y
        apply MonoidHom.ext
        intro z
        apply Subtype.ext
        change (β ((x : G) * (y : G)) (z : G) : Fˣ) =
          ((β (x : G) (z : G) * β (y : G) (z : G)) : Fˣ)
        rw [β.map_mul]
        rfl }
  let β2 := restricted 2 G2 h2
  let β3 := restricted 3 G3 h3
  have hz2 (x y : G2) : β2 x y = 1 ↔ β (x : G) (y : G) = 1 := by
    constructor
    · intro hh
      apply Subtype.ext
      exact congrArg (fun z : rootsOfUnity 2 F => (z : Fˣ)) hh
    · intro hh
      apply Subtype.ext
      exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) hh
  have hz3 (x y : G3) : β3 x y = 1 ↔ β (x : G) (y : G) = 1 := by
    constructor
    · intro hh
      apply Subtype.ext
      exact congrArg (fun z : rootsOfUnity 3 F => (z : Fˣ)) hh
    · intro hh
      apply Subtype.ext
      exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) hh
  have hskew (x y : G) : β x y * β y x = 1 := by
    have hh := ha (x * y)
    rw [β.map_mul] at hh
    change β x (x * y) * β y (x * y) = 1 at hh
    rw [(β x).map_mul, (β y).map_mul, ha x, ha y, one_mul, mul_one] at hh
    exact hh
  have hcross (a : G2) (b : G3) : β (a : G) (b : G) = 1 := by
    have hh2 := congrArg (fun f : G →* rootsOfUnity 6 F => f (b : G))
      (β.map_pow (a : G) 2)
    rw [h2 a, β.map_one] at hh2
    change 1 = β (a : G) (b : G) ^ 2 at hh2
    have hh3 := (β (a : G)).map_pow (b : G) 3
    rw [h3 b, map_one] at hh3
    change 1 = β (a : G) (b : G) ^ 3 at hh3
    have hh := hh3.symm
    rw [pow_succ, hh2.symm, one_mul] at hh
    exact hh
  have hcrossR (b : G3) (a : G2) : β (b : G) (a : G) = 1 := by
    have hh := hskew (a : G) (b : G)
    rw [hcross a b, one_mul] at hh
    exact hh
  have ha2 : ∀ x : G2, β2 x x = 1 := fun x => (hz2 x x).mpr (ha (x : G))
  have ha3 : ∀ x : G3, β3 x x = 1 := fun x => (hz3 x x).mpr (ha (x : G))
  have hn2 : ∀ x : G2, (∀ y : G2, β2 x y = 1) → x = 1 := by
    intro x hx
    apply Subtype.ext
    apply hn (x : G)
    intro y
    rw [← hright y]
    change β (x : G) ((π2 y : G) * (π3 y : G)) = 1
    rw [(β (x : G)).map_mul, (hz2 x (π2 y)).mp (hx (π2 y)), hcross, one_mul]
  have hn3 : ∀ x : G3, (∀ y : G3, β3 x y = 1) → x = 1 := by
    intro x hx
    apply Subtype.ext
    apply hn (x : G)
    intro y
    rw [← hright y]
    change β (x : G) ((π2 y : G) * (π3 y : G)) = 1
    rw [(β (x : G)).map_mul, hcrossR, (hz3 x (π3 y)).mp (hx (π3 y)), one_mul]
  have hiso2 : ∀ x ∈ E2, ∀ y ∈ E2, β2 x y = 1 := by
    intro x hx y hy
    exact (hz2 x y).mpr (hE (x : G) hx (y : G) hy)
  have hiso3 : ∀ x ∈ E3, ∀ y ∈ E3, β3 x y = 1 := by
    intro x hx y hy
    exact (hz3 x y).mpr (hE (x : G) hx (y : G) hy)
  obtain ⟨ζ, hζ⟩ := hmu
  have hζ2 : IsPrimitiveRoot (ζ ^ 3) 2 := by
    simpa using hζ.pow_of_dvd (by norm_num : (3 : ℕ) ≠ 0) (by norm_num : 3 ∣ 6)
  have hζ3 : IsPrimitiveRoot (ζ ^ 2) 3 := by
    simpa using hζ.pow_of_dvd (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : 2 ∣ 6)
  have hexp2 (x : G2) : x ^ 2 = 1 := by apply Subtype.ext; exact h2 x
  have hexp3 (x : G3) : x ^ 3 = 1 := by apply Subtype.ext; exact h3 x
  obtain ⟨B2, hB2, hc2⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_bdata_sol.prime_exponent_complement
      ⟨ζ ^ 3, hζ2⟩ hexp2 β2 ha2 hn2 E2 hsquare2 hiso2
  obtain ⟨B3, hB3, hc3⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_bdata_sol.prime_exponent_complement
      ⟨ζ ^ 2, hζ3⟩ hexp3 β3 ha3 hn3 E3 hsquare3 hiso3
  let B : Subgroup G := (B2.prod B3).map m
  have hisoB : ∀ x ∈ B, ∀ y ∈ B, β x y = 1 := by
    intro x hx y hy
    obtain ⟨a, haB, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hbB, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨ha2B, ha3B⟩ := Subgroup.mem_prod.mp haB
    obtain ⟨hb2B, hb3B⟩ := Subgroup.mem_prod.mp hbB
    change β ((a.1 : G) * (a.2 : G)) ((b.1 : G) * (b.2 : G)) = 1
    rw [β.map_mul]
    change β (a.1 : G) ((b.1 : G) * (b.2 : G)) *
      β (a.2 : G) ((b.1 : G) * (b.2 : G)) = 1
    rw [(β (a.1 : G)).map_mul, (β (a.2 : G)).map_mul,
      (hz2 a.1 b.1).mp (hB2 a.1 ha2B b.1 hb2B), hcross, hcrossR,
      (hz3 a.2 b.2).mp (hB3 a.2 ha3B b.2 hb3B)]
    simp
  have hdisjoint : Disjoint E B := by
    apply Subgroup.disjoint_def.mpr
    intro x hxE hxB
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hxB
    obtain ⟨hb2, hb3⟩ := Subgroup.mem_prod.mp hb
    have he2 : π2 (m b) ∈ E2 := E.pow_mem hxE 3
    have he3 : π3 (m b) ∈ E3 := E.pow_mem hxE 4
    rw [hleft2 b.1 b.2] at he2
    rw [hleft3 b.1 b.2] at he3
    have hb2eq : b.1 = 1 := Subgroup.disjoint_def.mp hc2.disjoint he2 hb2
    have hb3eq : b.2 = 1 := Subgroup.disjoint_def.mp hc3.disjoint he3 hb3
    change (b.1 : G) * (b.2 : G) = 1
    rw [hb2eq, hb3eq]
    simp
  have hcodisjoint : Codisjoint E B := by
    apply codisjoint_iff.mpr
    apply eq_top_iff.mpr
    intro x _
    have hxs2 : π2 x ∈ E2 ⊔ B2 := by
      rw [hc2.sup_eq_top]
      exact Subgroup.mem_top _
    have hxs3 : π3 x ∈ E3 ⊔ B3 := by
      rw [hc3.sup_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨e2, he2, b2, hb2, hm2⟩ := Subgroup.mem_sup.mp hxs2
    obtain ⟨e3, he3, b3, hb3, hm3⟩ := Subgroup.mem_sup.mp hxs3
    have he : m (e2, e3) ∈ E := E.mul_mem he2 he3
    have hb : m (b2, b3) ∈ B := ⟨(b2, b3), Subgroup.mem_prod.mpr ⟨hb2, hb3⟩, rfl⟩
    have hm : m (e2, e3) * m (b2, b3) = x := by
      rw [← m.map_mul]
      change m (e2 * b2, e3 * b3) = x
      rw [hm2, hm3]
      exact hright x
    exact Subgroup.mem_sup.mpr ⟨m (e2, e3), he, m (b2, b3), hb, hm⟩
  exact ⟨B, hisoB, ⟨hdisjoint, hcodisjoint⟩⟩

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
