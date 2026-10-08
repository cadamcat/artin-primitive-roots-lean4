import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GLOBAL-DATUM».TameGeometry

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- Orthogonality to local units forces the uniformizer exponent to be divisible by three. -/
theorem tameLocal_lagrangian (T : TorusRep D H v) (B : TameTorusBasis T)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (Q : TameLocalGeometry v) :
    ∀ x : (v.adicCompletion F)ˣ,
      x ∈ Q.Alag ↔ ∀ y ∈ Q.Alag, torusPairing D H v x y = 1 := by
  classical
  have he0 : B.e 0 ≠ 0 := B.linIndep.ne_zero 0
  have hid : (LinearMap.id : T.V →ₗ[ℂ] T.V) ≠ 0 := by
    intro h
    exact he0 (by simpa using DFunLike.congr_fun h (B.e 0))
  have hσ (x : (v.adicCompletion F)ˣ) : T.σa x ≠ 0 := by
    intro hx
    have h := T.σa_mul x x⁻¹
    rw [hx, LinearMap.zero_comp, mul_inv_cancel, T.σa_one] at h
    exact (smul_ne_zero (muThree D (H.hilb v x x⁻¹) : ℂˣ).ne_zero hid) h.symm
  have hcomm_pair (x y : (v.adicCompletion F)ˣ) :
      (T.σa x).comp (T.σa y) = (T.σa y).comp (T.σa x) ↔ torusPairing D H v x y = 1 := by
    constructor
    · intro h
      have h' := (T.σa_mul x y).symm.trans (h.trans (T.σa_mul y x))
      rw [mul_comm y x] at h'
      have hroot := rootsOfUnity.coe_injective (smul_left_injective ℂ (hσ (x * y)) h')
      rw [torusPairing, hroot, mul_inv_cancel]
    · intro h
      change muThree D (H.hilb v x y) * (muThree D (H.hilb v y x))⁻¹ = 1 at h
      have hroot := mul_inv_eq_one.mp h
      rw [T.σa_mul, T.σa_mul, mul_comm y x, hroot]
  have hdiag (x : (v.adicCompletion F)ˣ) (hx : x ∈ Q.Alag) (i : ZMod 3) :
      ∃ a : ℂ, T.σa x (B.e i) = a • B.e i := by
    obtain ⟨k, u, hu, rfl⟩ := (Q.mem_alag x).mp hx
    have hmod : ((3 * k : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨k, rfl⟩
    refine ⟨localChi D v u ^ (2 * (3 * k + 2 * (i.val : ℤ))), ?_⟩
    simpa only [hmod, add_zero] using B.act (3 * k) u hu i
  intro x
  constructor
  · intro hx y hy
    apply (hcomm_pair x y).mp
    apply LinearMap.ext_on_range B.spans
    intro i
    obtain ⟨a, ha⟩ := hdiag x hx i
    obtain ⟨b, hb⟩ := hdiag y hy i
    simp only [LinearMap.comp_apply, ha, hb, map_smul, smul_smul, mul_comm]
  · intro hx
    have hunit (u : (v.adicCompletion F)ˣ) (hu : IsLocUnit v u) :
        T.σa u (B.e 0) = B.e 0 := by
      simpa using B.act 0 u hu 0
    have hfixed : ∀ u, IsLocUnit v u → T.σa u (T.σa x (B.e 0)) = T.σa x (B.e 0) := by
      intro u hu
      have huL : u ∈ Q.Alag := (Q.mem_alag u).mpr ⟨0, u, hu, by simp⟩
      have h := LinearMap.congr_fun ((hcomm_pair x u).mpr (hx u huL)) (B.e 0)
      simpa only [LinearMap.comp_apply, hunit u hu] using h.symm
    obtain ⟨a, ha⟩ := tame_unitFixed T B hv (T.σa x (B.e 0)) hfixed
    obtain ⟨j, u, hu, hxj⟩ := Q.decomposition x
    have hact : T.σa x (B.e 0) = localChi D v u ^ (2 * j) • B.e (j : ZMod 3) := by
      rw [hxj]
      simpa using B.act j u hu 0
    have hχ6 := (localChi_basic (D := D) hv).2.2.2.1 u hu
    have hχ : localChi D v u ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num)] at hχ6
      exact zero_ne_one hχ6
    have hscalar : localChi D v u ^ (2 * j) ≠ 0 := zpow_ne_zero _ hχ
    let b : Module.Basis (ZMod 3) ℂ T.V := Module.Basis.mk B.linIndep (by rw [B.spans])
    have hb (i : ZMod 3) : b i = B.e i := Module.Basis.mk_apply _ _ i
    have hmod : (j : ZMod 3) = 0 := by
      by_contra hn
      have h := congrArg (b.coord (j : ZMod 3)) (hact.symm.trans ha)
      apply hscalar
      simpa [← hb, hn, Ne.symm hn] using h
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd j 3).mp hmod
    exact (Q.mem_alag x).mpr ⟨k, u, hu, by simpa only [hk, Nat.cast_ofNat] using hxj⟩

/-- The coordinate at zero is fixed by the tame Lagrangian and has the required normalization. -/
theorem tameLocal_evaluation (T : TorusRep D H v) (B : TameTorusBasis T)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (Q : TameLocalGeometry v) :
    ∃ lam : T.V →ₗ[ℂ] ℂ, lam ≠ 0 ∧
      (∀ y ∈ Q.Alag, ∀ x, lam (T.σa y x) = lam x) ∧
      ∀ k : ZMod 3, lam (B.e k) = if k = 0 then 1 else 0 := by
  classical
  let b : Module.Basis (ZMod 3) ℂ T.V := Module.Basis.mk B.linIndep (by rw [B.spans])
  let lam : T.V →ₗ[ℂ] ℂ := b.coord 0
  have hb (i : ZMod 3) : b i = B.e i := Module.Basis.mk_apply _ _ i
  have hnorm (i : ZMod 3) : lam (B.e i) = if i = 0 then 1 else 0 := by
    simp [lam, ← hb, Finsupp.single_apply]
  refine ⟨lam, ?_, ?_, hnorm⟩
  · intro h
    have hone : lam (B.e 0) = 1 := by simpa using hnorm 0
    have h' := DFunLike.congr_fun h (B.e 0)
    rw [hone] at h'
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using h')
  · intro y hy x
    obtain ⟨k, u, hu, hyu⟩ := (Q.mem_alag y).mp hy
    have hmod : ((3 * k : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨k, rfl⟩
    have hχ6 := (localChi_basic (D := D) hv).2.2.2.1 u hu
    have hpow : localChi D v u ^ (6 * k) = 1 := by
      calc
        localChi D v u ^ (6 * k) = (localChi D v u ^ (6 : ℕ)) ^ k := by
          rw [zpow_mul, zpow_ofNat]
        _ = 1 := by rw [hχ6]; simp
    have hzero : T.σa y (B.e 0) = B.e 0 := by
      rw [hyu, B.act (3 * k) u hu 0, hmod, zero_add]
      have hexp : 2 * (3 * k + 2 * ((0 : ZMod 3).val : ℤ)) = 6 * k := by
        simp only [ZMod.val_zero, Int.natCast_zero, mul_zero, add_zero]
        ring
      rw [hexp, hpow, one_smul]
    have hmap : lam.comp (T.σa y) = lam := by
      apply LinearMap.ext_on_range B.spans
      intro i
      change lam (T.σa y (B.e i)) = lam (B.e i)
      by_cases hi : i = 0
      · subst i
        rw [hzero]
      · rw [hyu, B.act (3 * k) u hu i, hmod, add_zero]
        simp only [map_smul, hnorm, if_neg hi, smul_zero]
    exact LinearMap.congr_fun hmap x

end ArtinPrimitiveRoots.A1.Theta
