import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.IdealMajorant

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- Local binary-class bounds and finite exceptional coordinates give absolute global convergence. -/
theorem whit_local_product_summable
    (L : ∀ v : FinPlace F, Subgroup (v.adicCompletion F)ˣ)
    (E : Finset (FinPlace F))
    (hL : ∀ v, v ∉ E → ∀ x : (v.adicCompletion F)ˣ,
      x ∈ L v ↔ ∃ (k : ℤ) (u : (v.adicCompletion F)ˣ),
        IsLocUnit v u ∧ x = unifLoc v ^ (3 * k) * u)
    (hfin : ∀ v, v ∈ E → Finite ((v.adicCompletion F)ˣ ⧸ L v))
    (a : FinPlace F → (Fˣ ⧸ whitRationalAlag L) → ℂ)
    (ha : ∀ q, (Function.mulSupport (fun v => a v q)).Finite)
    (σ : ℝ) (hσ : 1 < σ)
    (c : FinPlace F → ℝ) (hc : ∀ v ∈ E, 0 ≤ c v)
    (hbad : ∀ q v, v ∈ E → ‖a v q‖ ≤ c v)
    (hgood : ∀ q v, v ∉ E → ‖a v q‖ ≤
      if (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 0 then 1 else
        if (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 1 then qv v ^ (-σ) else 0) :
    Summable (fun q : Fˣ ⧸ whitRationalAlag L => ‖∏ᶠ v, a v q‖) := by
  let Q := Fˣ ⧸ whitRationalAlag L
  let f : Q → ℂ := fun q => ∏ᶠ v, a v q
  obtain ⟨supp, hsupp, hencode⟩ := whit_rational_class_encoding L E hL
  have hbinary (q : Q) (hq : f q ≠ 0) (v : FinPlace F) (hv : v ∉ E) :
      (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 0 ∨
        (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 1 := by
    by_cases hzero : (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 0
    · exact Or.inl hzero
    by_cases hone : (ordv v (toLoc v (Quotient.out q)) : ZMod 3) = 1
    · exact Or.inr hone
    have hb := hgood q v hv
    rw [if_neg hzero, if_neg hone] at hb
    have hz : a v q = 0 := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
    exact False.elim (hq (finprod_eq_zero (fun v => a v q) v hz (ha q)))
  let B := ∀ v : E, (v.1.adicCompletion F)ˣ ⧸ L v.1
  letI : ∀ v : E, Finite ((v.1.adicCompletion F)ˣ ⧸ L v.1) :=
    fun v => hfin v.1 v.2
  letI : Finite B := inferInstance
  let code : {q : Q // f q ≠ 0} → Ideal (𝓞 F) × B := fun q =>
    (whitPrimeSupportIdeal (supp q.1), fun v => whitAlagCoordinate L v.1 q.1)
  have hcode : Function.Injective code := by
    intro p p' hp
    apply Subtype.ext
    apply hencode p.1 p'.1 (hbinary p.1 p.2) (hbinary p'.1 p'.2)
    · exact congrArg Prod.fst hp
    · intro v hv
      exact congrFun (congrArg Prod.snd hp) ⟨v, hv⟩
  let N : ℂ →* ℝ := {
    toFun := norm
    map_one' := norm_one
    map_mul' := norm_mul
  }
  have hnorm (q : Q) : ‖f q‖ = ∏ᶠ v, ‖a v q‖ := N.map_finprod (ha q)
  have hnormFinite (q : Q) : (Function.mulSupport (fun v => ‖a v q‖)).Finite := by
    refine (ha q).subset ?_
    intro v hv
    change ‖a v q‖ ≠ 1 at hv
    change a v q ≠ 1
    intro h
    exact hv (by rw [h, norm_one])
  refine whit_ideal_norm_majorant f code hcode σ (∏ v ∈ E, c v) hσ
    (Finset.prod_nonneg (fun v hv => hc v hv)) ?_
  intro p
  let q := p.1
  have hq : f q ≠ 0 := p.2
  change ‖f q‖ ≤ (∏ v ∈ E, c v) *
    ArtinPrimitiveRoots.Hecke.idealNormRpowTerm σ (whitPrimeSupportIdeal (supp q))
  let g : FinPlace F → ℝ := fun v =>
    if v ∈ E then c v else if v ∈ supp q then qv v ^ (-σ) else 1
  have hgsub : Function.mulSupport g ⊆ (↑(E ∪ supp q) : Set (FinPlace F)) := by
    intro v hv
    change g v ≠ 1 at hv
    by_cases hvE : v ∈ E
    · exact Finset.mem_union_left _ hvE
    by_cases hvS : v ∈ supp q
    · exact Finset.mem_union_right _ hvS
    exact False.elim (hv (by simp only [g, if_neg hvE, if_neg hvS]))
  have hgfin : (Function.mulSupport g).Finite :=
    (E ∪ supp q).finite_toSet.subset hgsub
  have hpoint (v : FinPlace F) : ‖a v q‖ ≤ g v := by
    by_cases hvE : v ∈ E
    · simpa only [g, if_pos hvE] using hbad q v hvE
    by_cases hvS : v ∈ supp q
    · have hone := ((hsupp q v).mp hvS).2
      have hzero : (ordv v (toLoc v (Quotient.out q)) : ZMod 3) ≠ 0 := by
        rw [hone]
        exact one_ne_zero
      simpa only [g, if_neg hvE, if_pos hvS, if_neg hzero, if_pos hone] using hgood q v hvE
    · have hnotone : (ordv v (toLoc v (Quotient.out q)) : ZMod 3) ≠ 1 := by
        intro hone
        exact hvS ((hsupp q v).mpr ⟨hvE, hone⟩)
      have hzero := (hbinary q hq v hvE).resolve_right hnotone
      simpa only [g, if_neg hvE, if_neg hvS, if_pos hzero] using hgood q v hvE
  have hle : ‖f q‖ ≤ ∏ᶠ v, g v := by
    rw [hnorm]
    exact finprod_le_finprod₀ (hnormFinite q) (fun v => norm_nonneg _) hgfin hpoint
  have hdis : Disjoint E (supp q) := by
    apply Finset.disjoint_left.mpr
    intro v hvE hvS
    exact ((hsupp q v).mp hvS).1 hvE
  have hgprod : (∏ᶠ v, g v) =
      (∏ v ∈ E, c v) * ∏ v ∈ supp q, qv v ^ (-σ) := by
    rw [finprod_eq_finsetProd_of_mulSupport_subset g hgsub, Finset.prod_union hdis]
    congr 1
    · apply Finset.prod_congr rfl
      intro v hv
      simp only [g, if_pos hv]
    · apply Finset.prod_congr rfl
      intro v hv
      have hvE := ((hsupp q v).mp hv).1
      simp only [g, if_neg hvE, if_pos hv]
  have hI0 : Ideal.absNorm (whitPrimeSupportIdeal (supp q)) ≠ 0 := by
    intro h
    exact (whit_prime_support_encoding.2.1 (supp q)) (Ideal.absNorm_eq_zero_iff.mp h)
  have hterm : ArtinPrimitiveRoots.Hecke.idealNormRpowTerm σ
      (whitPrimeSupportIdeal (supp q)) = ∏ v ∈ supp q, qv v ^ (-σ) := by
    rw [ArtinPrimitiveRoots.Hecke.idealNormRpowTerm, if_neg hI0,
      whit_prime_support_encoding.2.2]
    exact (Real.finsetProd_rpow (supp q) qv
      (fun v _ => (lt_trans zero_lt_one (qv_gt_one v)).le) (-σ)).symm
  rw [hgprod, ← hterm] at hle
  exact hle

end ArtinPrimitiveRoots.A1.Theta
