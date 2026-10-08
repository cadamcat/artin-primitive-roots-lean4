import ArtinPrimitiveRoots.Spec.Main

set_option autoImplicit false
open NumberField MeasureTheory Function
open scoped Classical Pointwise
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
variable {F : Type} [Field F] [NumberField F]

/-- Integral comparison for a finite-index inclusion of countable period groups. -/
theorem cusp_integral_descent (Λ₀ Λ : AddSubgroup (InfinitePlace F → ℂ)) [Countable Λ]
    (hle : Λ₀ ≤ Λ) (hindex : Λ₀.relIndex Λ ≠ 0)
    (P₀ Pτ : Set (InfinitePlace F → ℂ))
    (hP₀ : IsAddFundamentalDomain Λ₀ P₀ volume)
    (hPτ : IsAddFundamentalDomain Λ Pτ volume)
    (f : (InfinitePlace F → ℂ) → ℂ)
    (hf : ∀ μ ∈ Λ, ∀ x, f (μ + x) = f x) (hzero : ∫ x in P₀, f x = 0) :
    ∫ x in Pτ, f x = 0 := by
  let V := InfinitePlace F → ℂ
  letI : Countable Λ₀ := Function.Injective.countable
    (f := fun h : Λ₀ => (⟨h.val, hle h.property⟩ : Λ))
    (by intro a b h; exact Subtype.ext (congrArg (fun x : Λ => (x : V)) h))
  let L := Λ₀.addSubgroupOf Λ
  let Q := Λ ⧸ L
  letI : Fintype Q := L.fintypeOfIndexNeZero hindex
  let r : Q → Λ := Quotient.out
  have hsplit (g : Λ) : ∃ q : Q, ∃ h : Λ₀, (g : V) = (r q : V) + (h : V) := by
    let q : Q := QuotientAddGroup.mk g
    have hg : g - r q ∈ L := QuotientAddGroup.eq_iff_sub_mem.mp
      (show (g : Q) = (r q : Q) from (Quotient.out_eq' q).symm)
    refine ⟨q, ⟨((g - r q : Λ) : V), hg⟩, ?_⟩
    change (g : V) = (r q : V) + ((g : V) - (r q : V))
    abel
  have hinj (a b : Λ₀) (q t : Q)
      (heq : (a : V) + (r q : V) = (b : V) + (r t : V)) : a = b ∧ q = t := by
    have hd : r q - r t ∈ L := by
      change (r q : V) - (r t : V) ∈ Λ₀
      have hh : (r q : V) - (r t : V) = (b : V) - (a : V) :=
        sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using heq)
      rw [hh]
      exact Λ₀.sub_mem b.property a.property
    have hqt : q = t := by
      have hh : (r q : Q) = (r t : Q) := QuotientAddGroup.eq_iff_sub_mem.mpr hd
      simpa only [r, Quotient.out_eq'] using hh
    subst t
    exact ⟨Subtype.ext (add_right_cancel heq), rfl⟩
  let C : Q → Set V := fun q => (r q : V) +ᵥ Pτ
  let T : Set V := ⋃ q, C q
  have hC (q : Q) : NullMeasurableSet (C q) volume :=
    hPτ.nullMeasurableSet_vadd (r q)
  have hcells : Pairwise (AEDisjoint volume on C) := by
    intro q t hqt
    apply hPτ.aedisjoint
    intro h
    exact hqt (Quotient.out_injective h)
  have hT : IsAddFundamentalDomain Λ₀ T volume := by
    refine ⟨NullMeasurableSet.iUnion hC, ?_, ?_⟩
    · filter_upwards [hPτ.ae_covers] with x hx
      obtain ⟨g, hg⟩ := hx
      obtain ⟨q, h, hh⟩ := hsplit (-g)
      refine ⟨-h, Set.mem_iUnion.mpr ⟨q, ?_⟩⟩
      change -(h : V) + x ∈ (r q : V) +ᵥ Pτ
      refine ⟨(g : V) + x, hg, ?_⟩
      change (r q : V) + ((g : V) + x) = -(h : V) + x
      have hh' : (r q : V) + (g : V) = -(h : V) := by
        rw [eq_neg_iff_add_eq_zero]
        calc
          (r q : V) + (g : V) + (h : V) = ((r q : V) + (h : V)) + (g : V) := by abel
          _ = 0 := by rw [← hh]; simp
      rw [← add_assoc, hh']
    · intro a b hab
      change AEDisjoint volume ((a : V) +ᵥ T) ((b : V) +ᵥ T)
      simp only [T, Set.vadd_set_iUnion, AEDisjoint.iUnion_left_iff,
        AEDisjoint.iUnion_right_iff]
      intro t q
      have hne : (⟨(a : V), hle a.property⟩ : Λ) + r q ≠
          (⟨(b : V), hle b.property⟩ : Λ) + r t := by
        intro heq
        exact hab (hinj a b q t (congrArg Subtype.val heq)).1
      have hd := hPτ.aedisjoint hne
      change AEDisjoint volume (((a : V) + (r q : V)) +ᵥ Pτ)
        (((b : V) + (r t : V)) +ᵥ Pτ) at hd
      simpa only [C, ← add_vadd] using hd
  have hTzero : ∫ x in T, f x = 0 := by
    rw [← hP₀.setIntegral_eq hT (fun μ x => hf μ (hle μ.property) x)]
    exact hzero
  have hCi (q : Q) : IntegrableOn f (C q) volume ↔ IntegrableOn f Pτ volume := by
    have hi := (measurePreserving_vadd (r q) volume).integrableOn_image
      (measurableEmbedding_const_vadd (r q)) (f := f) (s := Pτ)
    change IntegrableOn f (C q) volume ↔
      IntegrableOn (fun x => f ((r q : V) + x)) Pτ volume at hi
    simpa only [hf (r q) (r q).property] using hi
  have hCint (q : Q) : ∫ x in C q, f x = ∫ x in Pτ, f x := by
    have hi := (measurePreserving_vadd (r q) volume).setIntegral_image_emb
      (measurableEmbedding_const_vadd (r q)) f Pτ
    change (∫ x in C q, f x) = ∫ x in Pτ, f ((r q : V) + x) at hi
    simpa only [hf (r q) (r q).property] using hi
  by_cases hi : IntegrableOn f Pτ volume
  · have hiT : IntegrableOn f T volume :=
      integrableOn_finite_iUnion.mpr (fun q => (hCi q).mpr hi)
    have hsum : ∫ x in T, f x = (Fintype.card Q : ℂ) * ∫ x in Pτ, f x := by
      rw [show T = ⋃ q, C q from rfl, integral_iUnion_ae hC hcells hiT,
        tsum_fintype]
      simp only [hCint, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card Q : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card Q ≠ 0)
    exact (mul_eq_zero.mp (hsum.symm.trans hTzero)).resolve_left hn
  · exact integral_undef hi

end ArtinPrimitiveRoots.A1.Theta
