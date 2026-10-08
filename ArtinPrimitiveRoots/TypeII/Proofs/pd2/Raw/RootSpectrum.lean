import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootCRTData
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootCRTGraphSum

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_rootGamma (u S : ℕ) : (ZMod (u * pd2a_rootShared u S))ˣ :=
  (ZMod.unitOfCoprime (pd2a_rootUnshared u S) (pd2a_rootCRT_coprime u S).symm)⁻¹
noncomputable def pd2a_rootGammaOther (u S : ℕ) : (ZMod (pd2a_rootUnshared u S))ˣ :=
  (ZMod.unitOfCoprime (u * pd2a_rootShared u S) (pd2a_rootCRT_coprime u S))⁻¹

lemma pd2a_root_character_split (u S : ℕ) (hu : 0 < u) (hS : 0 < S) (hSq : Squarefree S)
    [NeZero (u * S)] [NeZero (u * pd2a_rootShared u S)] [NeZero (pd2a_rootUnshared u S)]
    (z : ZMod (u * S)) :
    ZMod.stdAddChar z =
      ZMod.stdAddChar ((pd2a_rootGamma u S : ZMod (u * pd2a_rootShared u S)) * (pd2a_rootCRTEquiv u S hSq z).1) *
        ZMod.stdAddChar ((pd2a_rootGammaOther u S : ZMod (pd2a_rootUnshared u S)) * (pd2a_rootCRTEquiv u S hSq z).2) := by
  let M := u * pd2a_rootShared u S
  let N := pd2a_rootUnshared u S
  have hM : 0 < M := mul_pos hu (pd2a_rootShared_pos u S)
  have hN : 0 < N := pd2a_rootUnshared_pos u S
  letI : NeZero (M * N) := ⟨(mul_pos hM hN).ne'⟩
  have hmod : u * S = M * N := by dsimp [M, N]; rw [mul_assoc, pd2a_rootShared_mul_unshared u S hSq]
  let ec : ZMod (u * S) ≃+* ZMod (M * N) := RingEquiv.cast (R := ZMod) hmod
  have hFirst : (pd2a_rootCRTEquiv u S hSq z).1 = ((ec z).val : ZMod M) :=
    pd2a_crt_first_val M N (pd2a_rootCRT_coprime u S) (ec z)
  have hSecond : (pd2a_rootCRTEquiv u S hSq z).2 = ((ec z).val : ZMod N) :=
    pd2a_crt_second_val M N (pd2a_rootCRT_coprime u S) (ec z)
  have h := pd2a_root_character_CRT M N hM hN (pd2a_rootCRT_coprime u S) (ec z)
  rw [pd2a_character_cast (u * S) (M * N) hmod z] at h
  simpa only [← hFirst, ← hSecond, pd2a_rootGamma, pd2a_rootGammaOther] using h

lemma pd2a_rootGraph_fourier_decomposition (u S : ℕ) (hu : 0 < u) (hS : 0 < S)
    [NeZero (u * S)] [NeZero (u * pd2a_rootShared u S)] [NeZero (pd2a_rootShared u S)]
    [NeZero (pd2a_rootUnshared u S)] (hSq : Squarefree S)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hdet : Matrix.det g₀ = 1)
    (hu₀ : (u : ZMod S) = g₀ 0 0) (h k : ZMod (u * S)) :
    ∃ αA : (ZMod (u * pd2a_rootShared u S))ˣ, ∃ phase : ℂ,
      ‖phase‖ = 1 ∧
      (αA : ZMod (u * pd2a_rootShared u S)) =
        (u : ZMod (u * pd2a_rootShared u S)) * ((g₀ 1 1).val : ZMod (u * pd2a_rootShared u S)) - 1 ∧
      pd2a_rootGraphTransform (u * S) (pd2a_rootGraph u S g₀) h k =
        phase * (pd2a_rootShared u S : ℂ)⁻¹ *
          ∑ j : ZMod (pd2a_rootShared u S),
            ZMod.stdAddChar (-j * ((g₀ 0 1).val : ZMod (pd2a_rootShared u S))) *
            ∑ c : (ZMod (u * pd2a_rootShared u S))ˣ,
              ZMod.stdAddChar (((pd2a_rootGamma u S : ZMod (u * pd2a_rootShared u S)) *
                  (h.val : ZMod (u * pd2a_rootShared u S)) +
                  (u : ZMod (u * pd2a_rootShared u S)) * (j.val : ZMod (u * pd2a_rootShared u S))) *
                  (c : ZMod (u * pd2a_rootShared u S)) +
                (pd2a_rootGamma u S : ZMod (u * pd2a_rootShared u S)) * (k.val : ZMod (u * pd2a_rootShared u S)) *
                  (αA : ZMod (u * pd2a_rootShared u S)) * ((c⁻¹ : (ZMod (u * pd2a_rootShared u S))ˣ) : ZMod (u * pd2a_rootShared u S))) := by
  let M := u * pd2a_rootShared u S
  let D := pd2a_rootShared u S
  let N := pd2a_rootUnshared u S
  letI : NeZero S := ⟨hS.ne'⟩
  let e := pd2a_rootCRTEquiv u S hSq
  let f : ZMod M →+* ZMod D := ZMod.castHom (dvd_mul_left D u) (ZMod D)
  let H : ZMod M := (pd2a_rootGamma u S : ZMod M) * (h.val : ZMod M)
  let K : ZMod M := (pd2a_rootGamma u S : ZMod M) * (k.val : ZMod M)
  let phase : ℂ := ZMod.stdAddChar ((pd2a_rootGammaOther u S : ZMod N) *
    ((h.val : ZMod N) * ((g₀ 0 1).val : ZMod N) + (k.val : ZMod N) * ((g₀ 1 0).val : ZMod N)))
  obtain ⟨αA, hαA, hPred⟩ := pd2a_rootGraph_split_data u S hu hS hSq g₀ hdet hu₀
  refine ⟨αA, phase, pd2a_root_character_norm N _, hαA, ?_⟩
  have hW : ∀ z ∈ pd2a_rootGraph u S g₀,
      ZMod.stdAddChar (h * z.1 + k * z.2) = phase * ZMod.stdAddChar (H * (e z.1).1 + K * (e z.2).1) := by
    intro z hz
    obtain ⟨hA, hcB, hvB, hcD⟩ := (hPred z).mp hz
    rw [pd2a_root_character_split u S hu hS hSq]
    have hLinearA : (e (h * z.1 + k * z.2)).1 =
        (h.val : ZMod M) * (e z.1).1 + (k.val : ZMod M) * (e z.2).1 := by
      simp only [e, map_add, map_mul, Prod.fst_add, Prod.fst_mul, pd2a_rootCRT_first_val]
    have hLinearB : (e (h * z.1 + k * z.2)).2 =
        (h.val : ZMod N) * ((g₀ 0 1).val : ZMod N) + (k.val : ZMod N) * ((g₀ 1 0).val : ZMod N) := by
      simp only [map_add, map_mul, Prod.snd_add, Prod.snd_mul]
      rw [show (e z.1).2 = ((g₀ 0 1).val : ZMod N) from hcB,
        show (e z.2).2 = ((g₀ 1 0).val : ZMod N) from hvB,
        pd2a_rootCRT_second_val u S hSq h, pd2a_rootCRT_second_val u S hSq k]
    rw [hLinearA, hLinearB]
    have hArg : (pd2a_rootGamma u S : ZMod M) * ((h.val : ZMod M) * (e z.1).1 + (k.val : ZMod M) * (e z.2).1) =
        H * (e z.1).1 + K * (e z.2).1 := by dsimp [H, K]; ring
    rw [hArg]
    exact mul_comm _ _
  have hsum := pd2a_crtGraph_sum e f αA ((g₀ 0 1).val : ZMod D)
    ((g₀ 0 1).val : ZMod N) ((g₀ 1 0).val : ZMod N) (pd2a_rootGraph u S g₀) hPred
    (fun z => ZMod.stdAddChar (h * z.1 + k * z.2)) phase H K ZMod.stdAddChar hW
  unfold pd2a_rootGraphTransform
  rw [hsum]
  have hfVal : ∀ c : (ZMod M)ˣ, f (c : ZMod M) = (((c : ZMod M).val : ℕ) : ZMod D) := by
    intro c
    conv_lhs => rw [← ZMod.natCast_zmod_val (c : ZMod M)]
    rw [map_natCast]
  simp_rw [hfVal]
  have hRestr := pd2a_restricted_inverse_fourier u D hu (pd2a_rootShared_pos u S) αA ((g₀ 0 1).val : ZMod D) H K
  have hFinal := congrArg (fun t : ℂ => phase * t) hRestr
  simp only [H, K, M, D, mul_assoc] at hFinal ⊢
  convert hFinal using 1 <;> congr!

end ArtinPrimitiveRoots.TypeII.PD
