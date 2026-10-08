import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootCRTData
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootCRTGraphSum

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd1c_rootGamma (u S : ℕ) : (ZMod (u * pd1c_rootShared u S))ˣ :=
  (ZMod.unitOfCoprime (pd1c_rootUnshared u S) (pd1c_rootCRT_coprime u S).symm)⁻¹
noncomputable def pd1c_rootGammaOther (u S : ℕ) : (ZMod (pd1c_rootUnshared u S))ˣ :=
  (ZMod.unitOfCoprime (u * pd1c_rootShared u S) (pd1c_rootCRT_coprime u S))⁻¹

lemma pd1c_root_character_split (u S : ℕ) (hu : 0 < u) (hS : 0 < S) (hSq : Squarefree S)
    [NeZero (u * S)] [NeZero (u * pd1c_rootShared u S)] [NeZero (pd1c_rootUnshared u S)]
    (z : ZMod (u * S)) :
    ZMod.stdAddChar z =
      ZMod.stdAddChar ((pd1c_rootGamma u S : ZMod (u * pd1c_rootShared u S)) * (pd1c_rootCRTEquiv u S hSq z).1) *
        ZMod.stdAddChar ((pd1c_rootGammaOther u S : ZMod (pd1c_rootUnshared u S)) * (pd1c_rootCRTEquiv u S hSq z).2) := by
  let M := u * pd1c_rootShared u S
  let N := pd1c_rootUnshared u S
  have hM : 0 < M := mul_pos hu (pd1c_rootShared_pos u S)
  have hN : 0 < N := pd1c_rootUnshared_pos u S
  letI : NeZero (M * N) := ⟨(mul_pos hM hN).ne'⟩
  have hmod : u * S = M * N := by dsimp [M, N]; rw [mul_assoc, pd1c_rootShared_mul_unshared u S hSq]
  let ec : ZMod (u * S) ≃+* ZMod (M * N) := RingEquiv.cast (R := ZMod) hmod
  have hFirst : (pd1c_rootCRTEquiv u S hSq z).1 = ((ec z).val : ZMod M) :=
    pd1c_crt_first_val M N (pd1c_rootCRT_coprime u S) (ec z)
  have hSecond : (pd1c_rootCRTEquiv u S hSq z).2 = ((ec z).val : ZMod N) :=
    pd1c_crt_second_val M N (pd1c_rootCRT_coprime u S) (ec z)
  have h := pd1c_root_character_CRT M N hM hN (pd1c_rootCRT_coprime u S) (ec z)
  rw [pd1c_character_cast (u * S) (M * N) hmod z] at h
  simpa only [← hFirst, ← hSecond, pd1c_rootGamma, pd1c_rootGammaOther] using h

lemma pd1c_rootGraph_fourier_decomposition (u S : ℕ) (hu : 0 < u) (hS : 0 < S)
    [NeZero (u * S)] [NeZero (u * pd1c_rootShared u S)] [NeZero (pd1c_rootShared u S)]
    [NeZero (pd1c_rootUnshared u S)] (hSq : Squarefree S)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hdet : Matrix.det g₀ = 1)
    (hu₀ : (u : ZMod S) = g₀ 0 0) (h k : ZMod (u * S)) :
    ∃ αA : (ZMod (u * pd1c_rootShared u S))ˣ, ∃ phase : ℂ,
      ‖phase‖ = 1 ∧
      (αA : ZMod (u * pd1c_rootShared u S)) =
        (u : ZMod (u * pd1c_rootShared u S)) * ((g₀ 1 1).val : ZMod (u * pd1c_rootShared u S)) - 1 ∧
      pd1c_rootGraphTransform (u * S) (pd1c_rootGraph u S g₀) h k =
        phase * (pd1c_rootShared u S : ℂ)⁻¹ *
          ∑ j : ZMod (pd1c_rootShared u S),
            ZMod.stdAddChar (-j * ((g₀ 0 1).val : ZMod (pd1c_rootShared u S))) *
            ∑ c : (ZMod (u * pd1c_rootShared u S))ˣ,
              ZMod.stdAddChar (((pd1c_rootGamma u S : ZMod (u * pd1c_rootShared u S)) *
                  (h.val : ZMod (u * pd1c_rootShared u S)) +
                  (u : ZMod (u * pd1c_rootShared u S)) * (j.val : ZMod (u * pd1c_rootShared u S))) *
                  (c : ZMod (u * pd1c_rootShared u S)) +
                (pd1c_rootGamma u S : ZMod (u * pd1c_rootShared u S)) * (k.val : ZMod (u * pd1c_rootShared u S)) *
                  (αA : ZMod (u * pd1c_rootShared u S)) * ((c⁻¹ : (ZMod (u * pd1c_rootShared u S))ˣ) : ZMod (u * pd1c_rootShared u S))) := by
  let M := u * pd1c_rootShared u S
  let D := pd1c_rootShared u S
  let N := pd1c_rootUnshared u S
  letI : NeZero S := ⟨hS.ne'⟩
  let e := pd1c_rootCRTEquiv u S hSq
  let f : ZMod M →+* ZMod D := ZMod.castHom (dvd_mul_left D u) (ZMod D)
  let H : ZMod M := (pd1c_rootGamma u S : ZMod M) * (h.val : ZMod M)
  let K : ZMod M := (pd1c_rootGamma u S : ZMod M) * (k.val : ZMod M)
  let phase : ℂ := ZMod.stdAddChar ((pd1c_rootGammaOther u S : ZMod N) *
    ((h.val : ZMod N) * ((g₀ 0 1).val : ZMod N) + (k.val : ZMod N) * ((g₀ 1 0).val : ZMod N)))
  obtain ⟨αA, hαA, hPred⟩ := pd1c_rootGraph_split_data u S hu hS hSq g₀ hdet hu₀
  refine ⟨αA, phase, pd1c_root_character_norm N _, hαA, ?_⟩
  have hW : ∀ z ∈ pd1c_rootGraph u S g₀,
      ZMod.stdAddChar (h * z.1 + k * z.2) = phase * ZMod.stdAddChar (H * (e z.1).1 + K * (e z.2).1) := by
    intro z hz
    obtain ⟨hA, hcB, hvB, hcD⟩ := (hPred z).mp hz
    rw [pd1c_root_character_split u S hu hS hSq]
    have hLinearA : (e (h * z.1 + k * z.2)).1 =
        (h.val : ZMod M) * (e z.1).1 + (k.val : ZMod M) * (e z.2).1 := by
      simp only [e, map_add, map_mul, Prod.fst_add, Prod.fst_mul, pd1c_rootCRT_first_val]
    have hLinearB : (e (h * z.1 + k * z.2)).2 =
        (h.val : ZMod N) * ((g₀ 0 1).val : ZMod N) + (k.val : ZMod N) * ((g₀ 1 0).val : ZMod N) := by
      simp only [map_add, map_mul, Prod.snd_add, Prod.snd_mul]
      rw [show (e z.1).2 = ((g₀ 0 1).val : ZMod N) from hcB,
        show (e z.2).2 = ((g₀ 1 0).val : ZMod N) from hvB,
        pd1c_rootCRT_second_val u S hSq h, pd1c_rootCRT_second_val u S hSq k]
    rw [hLinearA, hLinearB]
    have hArg : (pd1c_rootGamma u S : ZMod M) * ((h.val : ZMod M) * (e z.1).1 + (k.val : ZMod M) * (e z.2).1) =
        H * (e z.1).1 + K * (e z.2).1 := by dsimp [H, K]; ring
    rw [hArg]
    exact mul_comm _ _
  have hsum := pd1c_crtGraph_sum e f αA ((g₀ 0 1).val : ZMod D)
    ((g₀ 0 1).val : ZMod N) ((g₀ 1 0).val : ZMod N) (pd1c_rootGraph u S g₀) hPred
    (fun z => ZMod.stdAddChar (h * z.1 + k * z.2)) phase H K ZMod.stdAddChar hW
  unfold pd1c_rootGraphTransform
  rw [hsum]
  have hfVal : ∀ c : (ZMod M)ˣ, f (c : ZMod M) = (((c : ZMod M).val : ℕ) : ZMod D) := by
    intro c
    conv_lhs => rw [← ZMod.natCast_zmod_val (c : ZMod M)]
    rw [map_natCast]
  simp_rw [hfVal]
  have hRestr := pd1c_restricted_inverse_fourier u D hu (pd1c_rootShared_pos u S) αA ((g₀ 0 1).val : ZMod D) H K
  have hFinal := congrArg (fun t : ℂ => phase * t) hRestr
  simp only [H, K, M, D, mul_assoc] at hFinal ⊢
  convert hFinal using 1 <;> congr!

end ArtinPrimitiveRoots.TypeII.PD
