import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.TorusInd

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_lcoeff_sol

open NumberField IsDedekindDomain
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- The tame action appearing after inversion of the Jacquet parameter. -/
theorem tame_square_action (T : TorusRep D H v) (B : TameTorusBasis T)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (l : ℤ) (u : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u) (k : ZMod 3) :
    T.σa (-((unifLoc v ^ l * u) * (unifLoc v ^ l * u))) (B.e k) =
      (localChi D v u) ^ (2 * (l + (k.val : ℤ))) •
        B.e (k + 2 * (l : ZMod 3)) := by
  let O := v.adicCompletionIntegers F
  have hmul (a b : (v.adicCompletion F)ˣ)
      (ha : IsLocUnit v a) (hb : IsLocUnit v b) : IsLocUnit v (a * b) := by
    constructor
    · exact O.mul_mem (a : v.adicCompletion F) (b : v.adicCompletion F) ha.1 hb.1
    · simpa only [mul_inv_rev, Units.val_mul] using
        O.mul_mem ((b⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) hb.2 ha.2
  have hminus : IsLocUnit v (-1 : (v.adicCompletion F)ˣ) := by
    constructor <;> simp
  have hnegSquare : -(u * u) = (-1 : (v.adicCompletion F)ˣ) * (u * u) := by
    ext
    simp
  have hsquare : IsLocUnit v (u * u) := hmul u u hu hu
  have hneg : IsLocUnit v (-(u * u)) := by
    rw [hnegSquare]
    exact hmul (-1) (u * u) hminus hsquare
  obtain ⟨_, hχminus, hχmul, hχsix, _⟩ := localChi_basic (D := D) hv
  have hχsquare : localChi D v (-(u * u)) = localChi D v u ^ 2 := by
    rw [hnegSquare, hχmul (-1) (u * u) hminus hsquare, hχminus,
      hχmul u u hu hu, one_mul, pow_two]
  have hχ6 : localChi D v u ^ (6 : ℤ) = 1 := by
    simpa using hχsix u hu
  have hχne : localChi D v u ≠ 0 := by
    intro hzero
    have h := hχsix u hu
    rw [hzero, zero_pow (by decide : (6 : ℕ) ≠ 0)] at h
    exact zero_ne_one h
  have hpower :
      (localChi D v u ^ 2) ^ (2 * (2 * l + 2 * (k.val : ℤ))) =
        localChi D v u ^ (2 * (l + (k.val : ℤ))) := by
    rw [← zpow_natCast (localChi D v u) 2, ← zpow_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℤ) * (2 * (2 * l + 2 * (k.val : ℤ))) =
      2 * (l + (k.val : ℤ)) + 6 * (l + (k.val : ℤ)) by ring]
    have hperiod : localChi D v u ^ (6 * (l + (k.val : ℤ))) = 1 := by
      rw [zpow_mul, hχ6, one_zpow]
    rw [zpow_add₀ hχne, hperiod, mul_one]
  have hsplit :
      -((unifLoc v ^ l * u) * (unifLoc v ^ l * u)) =
        unifLoc v ^ (2 * l) * (-(u * u)) := by
    rw [show (2 : ℤ) * l = l + l by ring, zpow_add]
    ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  rw [hsplit, B.act (2 * l) (-(u * u)) hneg k, hχsquare, hpower]
  congr 2
  simp only [Int.cast_mul, Int.cast_ofNat]

end ArtinPrimitiveRoots.Proofs.th_lcoeff_sol
