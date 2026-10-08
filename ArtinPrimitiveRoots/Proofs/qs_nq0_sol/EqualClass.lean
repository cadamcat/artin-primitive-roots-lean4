import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ConductorBounds

/-!
# Sixth powers from the allowed-generator complement

The quotient of two allowed generators belongs to B. If it differs from
an S-unit by a diagonal element with trivial power class, it also belongs
to E. The complement condition then makes that quotient a sixth power
in the product of the S-completions.
-/

set_option autoImplicit false

open scoped NumberField
open NumberField ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- An allowed ratio whose power class comes from an S-unit is a sixth power at S. -/
theorem qs_nq0_allowed_ratio_sixth
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη) (H : HilbertData K) (Bd : BData Sd H)
    (a b x : Kˣ) (ha : Bd.Allowed a) (hb : Bd.Allowed b)
    (hunit : a / b / x ∈ Sd.US)
    (hx : (QuotientGroup.mk (Sd.diagU x) : Sd.V) = 1) :
    ∃ y : Sd.FSˣ, Sd.diagU (a / b) = y ^ 6 := by
  let q : Kˣ →* Sd.V := (QuotientGroup.mk' _).comp Sd.diagU
  change q a ∈ Bd.B at ha
  change q b ∈ Bd.B at hb
  change q x = 1 at hx
  have hB : q (a / b) ∈ Bd.B := by
    rw [map_div]
    exact Bd.B.div_mem ha hb
  have hE : q (a / b) ∈ Sd.E := by
    have hunitClass : q (a / b / x) ∈ Sd.E := by
      exact ⟨a / b / x, hunit, rfl⟩
    simpa only [map_div, hx, div_one] using hunitClass
  have hclass : q (a / b) = 1 :=
    (Subgroup.disjoint_def.mp Bd.compl.disjoint) hE hB
  have hpower : Sd.diagU (a / b) ∈ (powMonoidHom 6 : Sd.FSˣ →* Sd.FSˣ).range :=
    (QuotientGroup.eq_one_iff (Sd.diagU (a / b))).mp hclass
  obtain ⟨y, hy⟩ := hpower
  exact ⟨y, hy.symm⟩


/-- Local sixth powers at S give the trivial diagonal sixth-power class. -/
theorem qs_nq0_diagonal_sixth_class
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη) (x : Kˣ)
    (hx : ∀ v : FinPlace K, v ∈ Sd.Sf →
      ∃ y : (v.adicCompletion K)ˣ, toLoc v x = y ^ 6) :
    (QuotientGroup.mk (Sd.diagU x) : Sd.V) = 1 := by
  classical
  have hcomplex (w : InfinitePlace K) :
      ∃ y : ℂˣ, Units.map w.embedding.toMonoidHom x = y ^ 6 := by
    let z : ℂˣ := Units.map w.embedding.toMonoidHom x
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (n := 6) (by norm_num)
    have hy0 : y ≠ 0 := by
      intro hyzero
      have hz0 : (z : ℂ) = 0 := by rw [← hy, hyzero, zero_pow (by norm_num)]
      exact z.ne_zero hz0
    refine ⟨Units.mk0 y hy0, ?_⟩
    apply Units.ext
    exact hy.symm
  choose b hb using (fun v : Sd.Sf => hx v.1 v.2)
  choose c hc using hcomplex
  let y : Sd.FSˣ := {
    val := (fun v => (b v : v.1.adicCompletion K), fun w => (c w : ℂ))
    inv := (fun v => ((b v)⁻¹ : v.1.adicCompletion K), fun w => ((c w)⁻¹ : ℂ))
    val_inv := by ext v <;> simp
    inv_val := by ext v <;> simp }
  have hy : Sd.diagU x = y ^ 6 := by
    apply Units.ext
    apply Prod.ext
    · funext v
      change ((toLoc v.1 x : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) =
        (b v : v.1.adicCompletion K) ^ 6
      exact congrArg (fun u : (v.1.adicCompletion K)ˣ => (u : v.1.adicCompletion K)) (hb v)
    · funext w
      change w.embedding (x : K) = (c w : ℂ) ^ 6
      exact congrArg (fun u : ℂˣ => (u : ℂ)) (hc w)
  apply (QuotientGroup.eq_one_iff (Sd.diagU x)).mpr
  exact ⟨y, hy.symm⟩

end ArtinPrimitiveRoots.A2
