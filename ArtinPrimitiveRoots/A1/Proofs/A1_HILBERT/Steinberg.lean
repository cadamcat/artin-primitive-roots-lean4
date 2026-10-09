/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairing.
-/
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.SteinbergNorm
import ArtinPrimitiveRoots.A1.Proofs.A1_HILBERT.Nondegenerate

/-! Steinberg, skew, sixth-power annihilation, and the single-radical nondegeneracy law. -/

set_option autoImplicit false

open NumberField IsDedekindDomain KummerTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_hilbert_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

def hilbHomRight (D : FieldData F) (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
    (v.adicCompletion F)ˣ →* rootsOfUnity 6 F :=
  MonoidHom.mk' (fun b => hilb D v a b)
    (fun b c => (hilbert_mul_norm_criterion_H1 D).2 v a b c)

theorem hilb_steinberg (D : FieldData F) (v : FinPlace F)
    (a : (v.adicCompletion F)ˣ) (h : (1 : v.adicCompletion F) - a ≠ 0) :
    hilb D v a (Units.mk0 _ h) = 1 := by
  letI : ValuativeRel (v.adicCompletion F) := completionValuativeRel v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) := completionIsLocalField v
  change (rootEquiv D v).symm
    (simpleSymbolHom (v.adicCompletion F) six (completionSixNeZero v)
      (completionPrimitiveRoots D v) (Units.mk0 _ h) a) = 1
  exact (congrArg (rootEquiv D v).symm
    (simpleSymbolHom_steinberg (v.adicCompletion F) six
      (completionSixNeZero v) (completionPrimitiveRoots D v) a h)).trans
    (map_one (rootEquiv D v).symm)

private theorem hilb_neg_self (D : FieldData F) (v : FinPlace F)
    (a : (v.adicCompletion F)ˣ) : hilb D v a (-a) = 1 := by
  let K := v.adicCompletion F
  let B : Kˣ → Kˣ → rootsOfUnity 6 F := hilb D v
  have hmul_right (x y z : Kˣ) : B x (y * z) = B x y * B x z :=
    (hilbert_mul_norm_criterion_H1 D).2 v x y z
  have hinv_left (x y : Kˣ) : B x⁻¹ y = (B x y)⁻¹ :=
    map_inv (hilbHomLeft D v y) x
  have hone_left (y : Kˣ) : B 1 y = 1 := map_one (hilbHomLeft D v y)
  have hone_right (x : Kˣ) : B x 1 = 1 := map_one (hilbHomRight D v x)
  have hinv_right (x y : Kˣ) : B x y⁻¹ = (B x y)⁻¹ :=
    map_inv (hilbHomRight D v x) y
  change B a (-a) = 1
  by_cases ha : a = 1
  · subst a
    exact hone_left (-1)
  · have ha_val : (a : K) ≠ 1 := by
      intro h
      apply ha
      apply Units.ext
      exact h
    have hc0 : 1 - (a : K) ≠ 0 := by
      intro h
      exact ha_val (sub_eq_zero.mp h).symm
    have hd0 : 1 - ((a⁻¹ : Kˣ) : K) ≠ 0 := by
      intro h
      apply inv_ne_one.mpr ha_val
      simpa only [Units.val_inv_eq_inv_val] using (sub_eq_zero.mp h).symm
    let c : Kˣ := Units.mk0 (1 - (a : K)) hc0
    let d : Kˣ := Units.mk0 (1 - ((a⁻¹ : Kˣ) : K)) hd0
    have hd : d = (-c) * a⁻¹ := by
      apply Units.ext
      simp only [d, c, Units.val_mk0, Units.val_mul, Units.val_neg,
        Units.val_inv_eq_inv_val]
      change 1 - (a : K)⁻¹ = -(1 - (a : K)) * (a : K)⁻¹
      calc
        1 - (a : K)⁻¹ = ((a : K) - 1) * (a : K)⁻¹ := by
          rw [sub_mul, mul_inv_cancel₀ (Units.ne_zero a), one_mul]
        _ = -(1 - (a : K)) * (a : K)⁻¹ := by ring
    have hs1 : B a c = 1 := hilb_steinberg D v a hc0
    have hs2 : B a⁻¹ d = 1 := hilb_steinberg D v a⁻¹ hd0
    have hs2' : B a d = 1 := by
      rw [hinv_left] at hs2
      exact inv_eq_one.mp hs2
    have hdiag : B a (-c) = B a a := by
      rw [hd, hmul_right, hinv_right] at hs2'
      exact mul_inv_eq_one.mp hs2'
    have hc : c = (-1 : Kˣ) * (-c) := by simp
    have hneg_diag : B a (-1) * B a a = 1 := by
      rw [hc, hmul_right, hdiag] at hs1
      exact hs1
    rw [show -a = (-1 : Kˣ) * a by simp, hmul_right]
    exact hneg_diag

private theorem hilb_skew (D : FieldData F) (v : FinPlace F)
    (a b : (v.adicCompletion F)ˣ) : hilb D v a b * hilb D v b a = 1 := by
  let K := v.adicCompletion F
  let B : Kˣ → Kˣ → rootsOfUnity 6 F := hilb D v
  have hmul_left (x y z : Kˣ) : B (x * y) z = B x z * B y z :=
    (hilbert_mul_norm_criterion_H1 D).1 v x y z
  have hmul_right (x y z : Kˣ) : B x (y * z) = B x y * B x z :=
    (hilbert_mul_norm_criterion_H1 D).2 v x y z
  have hneg_self (x : Kˣ) : B x (-x) = 1 := hilb_neg_self D v x
  have hexpand : B (a * b) (-(a * b)) =
      (B a (-a) * B a b) * (B b (-b) * B b a) := by
    rw [hmul_left]
    congr 1
    · rw [show -(a * b) = (-a) * b by simp, hmul_right]
    · rw [show -(a * b) = (-b) * a by simp [mul_comm], hmul_right]
  calc
    B a b * B b a = (B a (-a) * B a b) * (B b (-b) * B b a) := by
      simp only [hneg_self, one_mul]
    _ = B (a * b) (-(a * b)) := hexpand.symm
    _ = 1 := hneg_self (a * b)

theorem hilbert_steinberg_skew_H2 (D : FieldData F) :
    (∀ v a b, hilb D v a b * hilb D v b a = 1) ∧
    (∀ v a b, (∃ c : (v.adicCompletion F)ˣ, a = c ^ 6) → hilb D v a b = 1) ∧
    (∀ (v : FinPlace F) (a : (v.adicCompletion F)ˣ)
      (h : (1 : v.adicCompletion F) - a ≠ 0),
      hilb D v a (Units.mk0 _ h) = 1) := by
  refine ⟨hilb_skew D, ?_, hilb_steinberg D⟩
  intro v a b ha
  obtain ⟨c, rfl⟩ := ha
  have hpow : (hilb D v c b) ^ 6 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 6 _).mp (hilb D v c b).property
  exact (map_pow (hilbHomLeft D v b) c 6).trans hpow

theorem hilbert_nondegenerate_H3 (D : FieldData F) :
    ∀ v a, (∀ b, hilb D v a b = 1) → ∃ c : (v.adicCompletion F)ˣ, a = c ^ 6 := by
  exact hilbert_nondegenerate_of_skew_H3 D (hilbert_steinberg_skew_H2 D).1

end ArtinPrimitiveRoots.Proofs.a1_hilbert_sol
