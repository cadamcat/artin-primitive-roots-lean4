import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.ProbeDenominators
import ArtinPrimitiveRoots.A2.Interface

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {μ : ∀ v : FinPlace F, Theta.LocHaar v} {v0 : InfinitePlace F}

/-- After the growing norm scale is removed, every weighted probe row lies in one
compact unit window, independently of the denominator and the translating unit. -/
theorem probe_row_window
    (D : FieldData F) (S : SData F CE condη)
    (G : SheetGeometry D S μ v0) (f0 : S.FS → ℂ) (f1 : ℝ → ℂ)
    (hf0compact : HasCompactSupport f0)
    (hf0units : ∀ x ∈ tsupport f0, IsUnit x)
    (hf1compact : HasCompactSupport f1)
    (hf1positive : tsupport f1 ⊆ Set.Ioi 0)
    (hf1continuous : Continuous f1) (hf1nonzero : ∃ v, f1 v ≠ 0) :
    ∃ K : Set S.FSˣ, IsCompact K ∧
      ∀ Z : ℝ, ∀ hZ : 2 ≤ Z, ∀ t : S.FSˣ, ∀ q : ℝ,
        f1 (q / (Z ^ b)) ≠ 0 → ∀ x : S.FS,
        f0 (x * ((t * G.ellU (q * (Z ^ a)))⁻¹ : S.FSˣ).val) ≠ 0 →
        ∃ y ∈ K, x =
          S.ell D (Z ^ M0) (Real.rpow_pos_of_pos (by linarith) M0) *
            ((t * y : S.FSˣ) : S.FS) := by
  classical
  obtain ⟨L, B, C, hL, hB, hC, hinterval, hmass⟩ :=
    probe_denominator_control S f1 hf1compact hf1positive hf1continuous hf1nonzero
  -- The inverse coordinates are continuous wherever all coordinates are units.
  have hunitContinuous {X : Type} [TopologicalSpace X] (g : X → S.FSˣ)
      (hg : Continuous (fun x => (g x : S.FS))) : Continuous g := by
    apply Units.continuous_iff.mpr
    refine ⟨hg, ?_⟩
    have hfin (v : S.Sf) :
        Continuous (fun x => (Ring.inverse (g x : S.FS)).1 v) := by
      have hcoord := (continuous_apply v).comp (continuous_fst.comp hg)
      have hnz (x : X) : (g x : S.FS).1 v ≠ 0 :=
        (Pi.isUnit_iff.mp (Prod.isUnit_iff.mp (g x).isUnit).1 v).ne_zero
      apply (hcoord.inv₀ hnz).congr
      intro x
      simp [Ring.inverse, (g x).isUnit]
    have harch (w : InfinitePlace F) :
        Continuous (fun x => (Ring.inverse (g x : S.FS)).2 w) := by
      have hcoord := (continuous_apply w).comp (continuous_snd.comp hg)
      have hnz (x : X) : (g x : S.FS).2 w ≠ 0 :=
        (Pi.isUnit_iff.mp (Prod.isUnit_iff.mp (g x).isUnit).2 w).ne_zero
      apply (hcoord.inv₀ hnz).congr
      intro x
      simp [Ring.inverse, (g x).isUnit]
    have hi : Continuous (fun x => Ring.inverse (g x : S.FS)) :=
      (continuous_pi hfin).prodMk (continuous_pi harch)
    exact hi.congr fun x => Ring.inverse_unit (g x)
  let X0 := {x : S.FS // x ∈ tsupport f0}
  let X1 := {v : ℝ // v ∈ Set.Icc L B}
  let lift : X0 → S.FSˣ := fun x => (hf0units x.1 x.2).unit
  have hliftVal (x : X0) : (lift x : S.FS) = x.1 :=
    (hf0units x.1 x.2).unit_spec
  have hlift : Continuous lift := by
    apply hunitContinuous
    exact continuous_subtype_val.congr fun x => (hliftVal x).symm
  have hX0 : IsCompact (Set.univ : Set X0) :=
    isCompact_iff_isCompact_univ.mp hf0compact.isCompact
  have hX1 : IsCompact (Set.univ : Set X1) :=
    isCompact_iff_isCompact_univ.mp (isCompact_Icc : IsCompact (Set.Icc L B))
  have hpositive (v : X1) : 0 < (v : ℝ) := hL.trans_le v.2.1
  have hell : Continuous (fun v : X1 => G.ellU v) := by
    apply hunitContinuous
    let e : ℝ := 1 / (2 * numComplex F)
    have hpow : Continuous (fun v : X1 => (v : ℝ) ^ e) :=
      continuous_subtype_val.rpow_const fun v => Or.inl (hpositive v).ne'
    have heq : (fun v : X1 => (G.ellU v : S.FS)) =
        fun v : X1 => ((fun _ : S.Sf => 1),
          fun _ : InfinitePlace F => (((v : ℝ) ^ e : ℝ) : ℂ)) := by
      funext v
      exact G.ellU_val v (hpositive v)
    rw [heq]
    exact continuous_const.prodMk
      (continuous_pi fun _ => Complex.continuous_ofReal.comp hpow)
  let shape : X0 × X1 → S.FSˣ := fun p => G.ellU p.2 * lift p.1
  let K : Set S.FSˣ := shape '' Set.univ
  have hshape : Continuous shape :=
    (hell.comp continuous_snd).mul (hlift.comp continuous_fst)
  have hK : IsCompact K := by
    apply IsCompact.image ?_ hshape
    simpa only [Set.univ_prod_univ] using hX0.prod hX1
  refine ⟨K, hK, ?_⟩
  intro Z hZ t q hq x hx
  have hZpos : 0 < Z := by linarith
  have hZb : 0 < Z ^ b := Real.rpow_pos_of_pos hZpos b
  have hN : 0 < Z ^ M0 := Real.rpow_pos_of_pos hZpos M0
  let v : ℝ := q / (Z ^ b)
  have hvSupport : v ∈ tsupport f1 :=
    subset_closure (Function.mem_support.mpr hq)
  have hvInterval : v ∈ Set.Icc L B := hinterval v hvSupport
  let vv : X1 := ⟨v, hvInterval⟩
  have hv : 0 < v := hpositive vv
  let u : X0 := ⟨x * ((t * G.ellU (q * (Z ^ a)))⁻¹ : S.FSˣ).val,
    subset_closure (Function.mem_support.mpr hx)⟩
  refine ⟨shape (u, vv), ⟨(u, vv), Set.mem_univ _, rfl⟩, ?_⟩
  have hscale : q * (Z ^ a) = Z ^ M0 * v := by
    rw [M0, Real.rpow_add hZpos]
    dsimp [v]
    field_simp
  have hqScale : 0 < q * (Z ^ a) := by
    rw [hscale]
    exact mul_pos hN hv
  have hellScale : (G.ellU (q * (Z ^ a)) : S.FS) =
      S.ell D (Z ^ M0) hN * (G.ellU v : S.FS) := by
    rw [G.ellU_val _ hqScale, G.ellU_val _ hv]
    simp only [SData.ell, hscale, Real.mul_rpow hN.le hv.le]
    ext j <;> simp
  calc
    x = (x * ((t * G.ellU (q * (Z ^ a)))⁻¹ : S.FSˣ).val) *
        ((t * G.ellU (q * (Z ^ a)) : S.FSˣ) : S.FS) := by
          simp [mul_assoc, ← Units.val_mul]
    _ = (t : S.FS) * (G.ellU (q * (Z ^ a)) : S.FS) * (lift u : S.FS) := by
          rw [hliftVal]
          simp only [Units.val_mul]
          dsimp [u]
          ac_rfl
    _ = S.ell D (Z ^ M0) hN * ((t * shape (u, vv) : S.FSˣ) : S.FS) := by
          rw [hellScale]
          simp only [shape, Units.val_mul]
          dsimp [vv]
          ac_rfl

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
