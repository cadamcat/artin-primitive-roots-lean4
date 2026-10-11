import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.ideal_S_exterior_split_count
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.sComponent_sign_partition
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_exterior_sieve_bound
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_family_card_bound
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_log_power_absorb

set_option autoImplicit false
set_option maxHeartbeats 600000
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem conductorIdealValue_mul
    (ω : A1.HeckeChar F) (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ω.idealValue (I * J) = ω.idealValue I * ω.idealValue J := by
  classical
  simp only [A1.HeckeChar.idealValue,
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,
    Multiset.map_add, Multiset.prod_add]

private theorem conductorIdealNorm_pos_of_ne_bot
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : 0 < idealNorm I := by
  have hne : Ideal.absNorm I ≠ 0 := by
    intro h
    exact hI (Ideal.absNorm_eq_zero_iff.mp h)
  change (Ideal.absNorm I : ℝ) > 0
  exact_mod_cast Nat.pos_of_ne_zero hne

private theorem conductorNorm_sum_sq_le_card
    {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have htriangle := norm_sum_le s f
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  have hcauchy' : (∑ i ∈ s, ‖f i‖) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by simpa using hcauchy
  exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htriangle).trans hcauchy'

private theorem conductorNorm_add_sq_le
    (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  calc
    ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (norm_add_le x y)
    _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

private theorem conductorCutoff_norm_le
    (N : ℝ) (hN : 0 ≤ N) (I : Ideal (𝓞 F))
    (hI : I ∈ conductorIdealCutoff F N) : idealNorm I ≤ N := by
  change I ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).toFinset at hI
  have hn := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).mem_toFinset.mp hI
  exact (Nat.le_floor_iff hN).1 hn

private theorem conductor_log_coeff_rearrange
    (A B C D x : ℝ) (k : ℕ) :
    A * (B * x ^ k) * (C * D * x) = A * B * C * D * x ^ (k + 1) := by
  calc
    A * (B * x ^ k) * (C * D * x) = A * B * C * D * (x ^ k * x) := by ac_rfl
    _ = A * B * C * D * x ^ (k + 1) := by rw [← pow_succ]

/-- Assemble the exact nonzero S-piece partition and local groups, absorb the
logarithms, and split off the bottom ideal using its quadratic family count.
Uses ideal_S_exterior_split_count, sComponent_sign_partition,
conductor_exterior_sieve_bound, conductor_family_card_bound, conductor_log_power_absorb.
Consumer: the exact frozen lem_conductor_sieve; no bottom multiplicativity is used. -/
theorem conductor_sieve_assemble (S : A1.SData F CE condη)
    (C₀ : ℝ) (hC₀ : 0 < C₀) (𝓛S : Finset (SLocalCharacter S)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ N U : ℝ, 2 ≤ N → 2 ≤ U →
        ∀ 𝓧 : Finset (A1.HeckeChar F), ConductorFamily S C₀ U 𝓛S 𝓧 →
          ∀ b : Ideal (𝓞 F) → ℂ,
            (∑ ω ∈ 𝓧, ‖∑ I ∈ conductorIdealCutoff F N, b I * ω.idealValue I‖ ^ 2) ≤
                C * (N + U ^ 2) * Real.rpow (N * U) ε *
                ∑ I ∈ conductorIdealCutoff F N, ‖b I‖ ^ 2 := by
  classical
  intro ε hε
  obtain ⟨Cext, hCext, hsieve⟩ := conductor_exterior_sieve_bound S C₀ hC₀
  obtain ⟨Cfam, hCfam, hfamilyCount⟩ :=
    conductor_family_card_bound S C₀ hC₀ 𝓛S
  obtain ⟨Clog, hClog, hlogAbsorb⟩ :=
    conductor_log_power_absorb (S.Sf.card + 1) ε hε
  rcases ideal_S_exterior_split_count S with ⟨hsplit, hpiecesData, hmassPart⟩
  rcases hpiecesData with ⟨Csp, hCsp, hpieceCount⟩
  let Cpair : ℝ := max 1 (𝓛S.card : ℝ) *
    (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces F
  have hCpair : 0 < Cpair := by
    dsimp [Cpair]
    positivity
  let Cnz : ℝ := Cpair * Csp * Cext * Clog
  have hCnz : 0 < Cnz := by
    dsimp [Cnz]
    positivity
  let C : ℝ := 2 * Cfam + 2 * Cnz
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N U hN hU 𝓧 h𝓧 b
  have hNnonneg : 0 ≤ N := by linarith
  let A := conductorIdealCutoff F N
  let B := A.filter (fun I => I ≠ ⊥)
  let Jset := conductorSPieces S N
  let Piece (J : Ideal (𝓞 F)) := B.filter (fun I => conductorSPart S I = J)
  let pairOf (ω : A1.HeckeChar F) := (SComponent S ω, conductorInfiniteComponent ω)
  let P : Finset (SLocalCharacter S × ConductorInfiniteLocal F) := 𝓧.image pairOf
  let Xp (p : SLocalCharacter S × ConductorInfiniteLocal F) :=
    𝓧.filter (fun ω => pairOf ω = p)
  have hfamilyParts : ∀ ω ∈ 𝓧,
      IsOfFinOrder ω ∧ SComponent S ω ∈ 𝓛S ∧
        ∃ f, IsPrimitiveConductor ω f ∧ idealNorm f ≤ C₀ * U := by
    intro ω hω
    change IsOfFinOrder ω ∧ SComponent S ω ∈ 𝓛S ∧
      ∃ f, IsPrimitiveConductor ω f ∧ idealNorm f ≤ C₀ * U
    exact h𝓧 ω hω
  have hfiniteLocal : ∀ ω ∈ 𝓧, IsOfFinOrder ω ∧ SComponent S ω ∈ 𝓛S := by
    intro ω hω
    exact ⟨(hfamilyParts ω hω).1, (hfamilyParts ω hω).2.1⟩
  have hsign := sComponent_sign_partition S 𝓛S 𝓧 hfiniteLocal
  rcases hsign with ⟨_, hPcard, hsignPart, hsupportedValue⟩
  have hXpGroup (p : SLocalCharacter S × ConductorInfiniteLocal F) :
      ConductorGroup S C₀ U p.1 p.2 (Xp p) := by
    intro ω hω
    have hω' : ω ∈ 𝓧 := (Finset.mem_filter.mp hω).1
    have hp : pairOf ω = p := (Finset.mem_filter.mp hω).2
    obtain ⟨hfin, hlocal, f, hf, hfb⟩ := hfamilyParts ω hω'
    have hp₁ : SComponent S ω = p.1 := congrArg Prod.fst hp
    have hp₂ : conductorInfiniteComponent ω = p.2 := congrArg Prod.snd hp
    exact ⟨hfin, hp₁, hp₂, f, hf, hfb⟩
  have hpairMap : (𝓧 : Set (A1.HeckeChar F)).MapsTo pairOf P := by
    intro ω hω
    exact Finset.mem_image_of_mem pairOf hω
  have hpairPartition (f : A1.HeckeChar F → ℝ) :
      (∑ ω ∈ 𝓧, f ω) = ∑ p ∈ P, ∑ ω ∈ Xp p, f ω := by
    have h := (Finset.sum_fiberwise_of_maps_to hpairMap f).symm
    simpa [P, Xp] using h
  have hpieceMap : (B : Set (Ideal (𝓞 F))).MapsTo (conductorSPart S) Jset := by
    intro I hI
    change conductorSPart S I ∈
      ((conductorIdealCutoff F N).filter (fun I => I ≠ ⊥)).image (conductorSPart S)
    exact Finset.mem_image_of_mem (conductorSPart S) (by simpa [B, A] using hI)
  have hpiecePartition (ω : A1.HeckeChar F) :
      (∑ I ∈ B, b I * ω.idealValue I) =
        ∑ J ∈ Jset, ∑ I ∈ Piece J, b I * ω.idealValue I := by
    have h := (Finset.sum_fiberwise_of_maps_to hpieceMap
      (fun I => b I * ω.idealValue I)).symm
    simpa [B, A, Jset, Piece, conductorSPieces, Finset.filter_filter,
      and_assoc, and_comm, and_left_comm] using h
  have hmassPieces :
      (∑ J ∈ Jset, ∑ I ∈ Piece J, ‖b I‖ ^ 2) =
        ∑ I ∈ B, ‖b I‖ ^ 2 := by
    simpa [B, A, Jset, Piece, conductorSPieces, Finset.filter_filter,
      and_assoc, and_comm, and_left_comm] using hmassPart N b
  have hJinfo (J : Ideal (𝓞 F)) (hJ : J ∈ Jset) :
      ConductorSupportedAtS S J ∧ idealNorm J ≤ N := by
    have hJ' : J ∈ ((conductorIdealCutoff F N).filter (fun I => I ≠ ⊥)).image
        (conductorSPart S) := by simpa [Jset, conductorSPieces] using hJ
    rcases Finset.mem_image.mp hJ' with ⟨I, hI, hEq⟩
    have hIbot : I ≠ ⊥ := (Finset.mem_filter.mp hI).2
    rcases hsplit I hIbot with ⟨hSupported, _, _, hnormS, _, _⟩
    constructor
    · simpa [hEq] using hSupported
    · calc
        idealNorm J = idealNorm (conductorSPart S I) := by rw [hEq]
        _ ≤ idealNorm I := by
          change (Ideal.absNorm (conductorSPart S I) : ℝ) ≤ (Ideal.absNorm I : ℝ)
          exact_mod_cast hnormS
        _ ≤ N := conductorCutoff_norm_le N hNnonneg I ((Finset.mem_filter.mp hI).1)
  have hpieceBot (J : Ideal (𝓞 F)) (x : {I : Ideal (𝓞 F) // I ∈ Piece J}) :
      x.1 ≠ ⊥ := (Finset.mem_filter.mp ((Finset.mem_filter.mp x.2).1)).2
  let ePart (J : Ideal (𝓞 F)) (x : {I : Ideal (𝓞 F) // I ∈ Piece J}) : S.ExtIdeal :=
    ⟨conductorExteriorPart S x.1, (hsplit x.1 (hpieceBot J x)).2.1⟩
  have hfactorPart (J : Ideal (𝓞 F)) (x : {I : Ideal (𝓞 F) // I ∈ Piece J}) :
      x.1 = J * (ePart J x).1 := by
    have hJ : conductorSPart S x.1 = J := (Finset.mem_filter.mp x.2).2
    have hdecomp := (hsplit x.1 (hpieceBot J x)).2.2.1
    rw [hJ] at hdecomp
    simpa [ePart] using hdecomp
  have hePartInj (J : Ideal (𝓞 F)) :
      Set.InjOn (ePart J) ((Piece J).attach : Set {I : Ideal (𝓞 F) // I ∈ Piece J}) := by
    intro x hx y hy hxy
    apply Subtype.ext
    have hxy' : (ePart J x).1 = (ePart J y).1 := congrArg Subtype.val hxy
    calc
      x.1 = J * (ePart J x).1 := hfactorPart J x
      _ = J * (ePart J y).1 := by rw [hxy']
      _ = y.1 := (hfactorPart J y).symm
  let Eimage (J : Ideal (𝓞 F)) : Finset S.ExtIdeal := (Piece J).attach.image (ePart J)
  have hEimageSubset (J : Ideal (𝓞 F)) :
      Eimage J ⊆ conductorExteriorCutoff S N := by
    intro E hE
    rcases Finset.mem_image.mp hE with ⟨x, hx, rfl⟩
    rcases hsplit x.1 (hpieceBot J x) with ⟨_, _, _, _, hnormE, _⟩
    have hcutI : x.1 ∈ A :=
      (Finset.mem_filter.mp ((Finset.mem_filter.mp x.2).1)).1
    have hNormE : idealNorm (ePart J x).1 ≤ N := by
      calc
        idealNorm (ePart J x).1 ≤ idealNorm x.1 := by
          change (Ideal.absNorm (conductorExteriorPart S x.1) : ℝ) ≤ (Ideal.absNorm x.1 : ℝ)
          exact_mod_cast hnormE
        _ ≤ N := conductorCutoff_norm_le N hNnonneg x.1 hcutI
    exact conductorExteriorCutoff_mem_of_norm S N hNnonneg (ePart J x) hNormE
  let bJ (J : Ideal (𝓞 F)) (E : S.ExtIdeal) : ℂ :=
    if E ∈ Eimage J then b (J * E.1) else 0
  have hfilterE (J : Ideal (𝓞 F)) :
      (conductorExteriorCutoff S N).filter (fun E => E ∈ Eimage J) = Eimage J := by
    apply Finset.Subset.antisymm
    · intro E hE
      exact (Finset.mem_filter.mp hE).2
    · intro E hE
      exact Finset.mem_filter.mpr ⟨hEimageSubset J hE, hE⟩
  have hsumPiece (J : Ideal (𝓞 F)) (hJ : J ∈ Jset) (ω : A1.HeckeChar F) :
      (∑ I ∈ Piece J, b I * ω.idealValue I) =
        ω.idealValue J *
          ∑ E ∈ conductorExteriorCutoff S N, bJ J E * ω.idealValue E.1 := by
    have hsumImage :
        (∑ x ∈ (Piece J).attach, b x.1 * ω.idealValue x.1) =
          ∑ E ∈ Eimage J, b (J * E.1) * ω.idealValue (J * E.1) := by
      calc
        _ = ∑ x ∈ (Piece J).attach, b (J * (ePart J x).1) *
              ω.idealValue (J * (ePart J x).1) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [← hfactorPart J x]
        _ = ∑ E ∈ Eimage J, b (J * E.1) * ω.idealValue (J * E.1) := by
              simpa [Eimage] using
                (Finset.sum_image (f := fun E : S.ExtIdeal =>
                  b (J * E.1) * ω.idealValue (J * E.1)) (g := ePart J)
                  (hePartInj J)).symm
    calc
      _ = ∑ x ∈ (Piece J).attach, b x.1 * ω.idealValue x.1 :=
        (Finset.sum_attach (Piece J) _).symm
      _ = ∑ E ∈ Eimage J, b (J * E.1) * ω.idealValue (J * E.1) := hsumImage
      _ = ∑ E ∈ Eimage J, ω.idealValue J * (b (J * E.1) * ω.idealValue E.1) := by
        apply Finset.sum_congr rfl
        intro E hE
        rcases Finset.mem_image.mp hE with ⟨x, hx, rfl⟩
        have hJne := (hJinfo J hJ).1.1
        rw [conductorIdealValue_mul ω J (ePart J x).1 hJne (ePart J x).2.1]
        ring
      _ = ω.idealValue J * ∑ E ∈ Eimage J, b (J * E.1) * ω.idealValue E.1 := by
        rw [Finset.mul_sum]
      _ = ω.idealValue J *
            ∑ E ∈ conductorExteriorCutoff S N, bJ J E * ω.idealValue E.1 := by
        congr 1
        calc
          _ = ∑ E ∈ (conductorExteriorCutoff S N).filter (fun E => E ∈ Eimage J),
                b (J * E.1) * ω.idealValue E.1 := by rw [hfilterE J]
          _ = ∑ E ∈ conductorExteriorCutoff S N,
                if E ∈ Eimage J then b (J * E.1) * ω.idealValue E.1 else 0 := by
                rw [Finset.sum_filter]
          _ = _ := by
                apply Finset.sum_congr rfl
                intro E hE
                simp [bJ]
  have hmassJ (J : Ideal (𝓞 F)) :
      (∑ E ∈ conductorExteriorCutoff S N, ‖bJ J E‖ ^ 2) =
        ∑ I ∈ Piece J, ‖b I‖ ^ 2 := by
    calc
      _ = ∑ E ∈ conductorExteriorCutoff S N,
            if E ∈ Eimage J then ‖b (J * E.1)‖ ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro E hE
          by_cases hEi : E ∈ Eimage J <;> simp [bJ, hEi]
      _ = ∑ E ∈ (conductorExteriorCutoff S N).filter (fun E => E ∈ Eimage J),
            ‖b (J * E.1)‖ ^ 2 := by rw [← Finset.sum_filter]
      _ = ∑ E ∈ Eimage J, ‖b (J * E.1)‖ ^ 2 := by rw [hfilterE J]
      _ = ∑ x ∈ (Piece J).attach, ‖b x.1‖ ^ 2 := by
          simpa only [hfactorPart J] using
            (Finset.sum_image (f := fun E : S.ExtIdeal => ‖b (J * E.1)‖ ^ 2)
              (g := ePart J) (hePartInj J))
      _ = ∑ I ∈ Piece J, ‖b I‖ ^ 2 := by
        simpa using (Finset.sum_attach (Piece J) (fun I => ‖b I‖ ^ 2))
  let Kext : ℝ := Cext * (N + U ^ 2) * (1 + Real.log N)
  have hlogNnonneg : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogBasePos : 0 < 1 + Real.log N := by linarith
  have hKextNonneg : 0 ≤ Kext := by dsimp [Kext]; positivity
  have hpiecePoint (J : Ideal (𝓞 F)) (hJ : J ∈ Jset)
      (ω : A1.HeckeChar F) (hω : ω ∈ 𝓧) :
      ‖∑ I ∈ Piece J, b I * ω.idealValue I‖ ^ 2 ≤
        ‖∑ E ∈ conductorExteriorCutoff S N, bJ J E * ω.idealValue E.1‖ ^ 2 := by
    rw [hsumPiece J hJ ω]
    have hlocal : ‖ω.idealValue J‖ ≤ 1 :=
      (hsupportedValue ω ω (hfamilyParts ω hω).1 (hfamilyParts ω hω).1 rfl J
        (hJinfo J hJ).1).2
    have hnorm :
        ‖ω.idealValue J * ∑ E ∈ conductorExteriorCutoff S N,
          bJ J E * ω.idealValue E.1‖ ≤
          ‖∑ E ∈ conductorExteriorCutoff S N, bJ J E * ω.idealValue E.1‖ := by
      rw [norm_mul]
      calc
        ‖ω.idealValue J‖ *
            ‖∑ E ∈ conductorExteriorCutoff S N, bJ J E * ω.idealValue E.1‖ ≤
          1 * ‖∑ E ∈ conductorExteriorCutoff S N, bJ J E * ω.idealValue E.1‖ :=
          mul_le_mul_of_nonneg_right hlocal (norm_nonneg _)
        _ = _ := by simp
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
  have hpieceBound (p : SLocalCharacter S × ConductorInfiniteLocal F)
      (J : Ideal (𝓞 F)) (hJ : J ∈ Jset) :
      (∑ ω ∈ Xp p, ‖∑ I ∈ Piece J, b I * ω.idealValue I‖ ^ 2) ≤
        Kext * ∑ I ∈ Piece J, ‖b I‖ ^ 2 := by
    have h := hsieve N U hN hU p.1 p.2 (Xp p) (hXpGroup p) (bJ J)
    calc
      _ ≤ ∑ ω ∈ Xp p,
            ‖∑ E ∈ conductorExteriorCutoff S N, bJ J E * ω.idealValue E.1‖ ^ 2 :=
          Finset.sum_le_sum (fun ω hω => hpiecePoint J hJ ω ((Finset.mem_filter.mp hω).1))
      _ ≤ Kext * ∑ E ∈ conductorExteriorCutoff S N, ‖bJ J E‖ ^ 2 := by
          simpa [Kext] using h
      _ = Kext * ∑ I ∈ Piece J, ‖b I‖ ^ 2 := by rw [hmassJ J]
  have hgroupNonzero (p : SLocalCharacter S × ConductorInfiniteLocal F)
      (hp : p ∈ P) :
      (∑ ω ∈ Xp p, ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2) ≤
        (Jset.card : ℝ) * Kext * ∑ I ∈ B, ‖b I‖ ^ 2 := by
    calc
      _ ≤ ∑ ω ∈ Xp p,
            (Jset.card : ℝ) * ∑ J ∈ Jset,
              ‖∑ I ∈ Piece J, b I * ω.idealValue I‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro ω hω
          rw [hpiecePartition ω]
          exact conductorNorm_sum_sq_le_card Jset
            (fun J => ∑ I ∈ Piece J, b I * ω.idealValue I)
      _ = (Jset.card : ℝ) *
            ∑ J ∈ Jset, ∑ ω ∈ Xp p,
              ‖∑ I ∈ Piece J, b I * ω.idealValue I‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (Jset.card : ℝ) *
            ∑ J ∈ Jset, Kext * ∑ I ∈ Piece J, ‖b I‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum (fun J hJ => hpieceBound p J hJ)
          · exact Nat.cast_nonneg _
      _ = (Jset.card : ℝ) * Kext *
            ∑ J ∈ Jset, ∑ I ∈ Piece J, ‖b I‖ ^ 2 := by
          rw [← Finset.mul_sum]
          ring
      _ = (Jset.card : ℝ) * Kext * ∑ I ∈ B, ‖b I‖ ^ 2 := by rw [hmassPieces]
  have hPcardR : (P.card : ℝ) ≤ Cpair := by
    have hpairCardR : (P.card : ℝ) ≤ (𝓛S.card : ℝ) *
        (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces F := by exact_mod_cast hPcard
    calc
      (P.card : ℝ) ≤ (𝓛S.card : ℝ) *
          (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces F := hpairCardR
      _ ≤ Cpair := by
        dsimp [Cpair]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hJcardR : (Jset.card : ℝ) ≤ Csp * (1 + Real.log N) ^ S.Sf.card := by
    simpa [Jset] using hpieceCount N hN
  have hnonzeroBound :
      (∑ ω ∈ 𝓧, ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2) ≤
        Cnz * (N + U ^ 2) * Real.rpow (N * U) ε * ∑ I ∈ B, ‖b I‖ ^ 2 := by
    have hpart := hpairPartition (fun ω => ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2)
    have hraw :
        (∑ ω ∈ 𝓧, ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2) ≤
          (P.card : ℝ) * (Jset.card : ℝ) * Kext * ∑ I ∈ B, ‖b I‖ ^ 2 := by
      calc
        _ = ∑ p ∈ P, ∑ ω ∈ Xp p,
              ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2 := hpart
        _ ≤ ∑ p ∈ P,
              (Jset.card : ℝ) * Kext * ∑ I ∈ B, ‖b I‖ ^ 2 :=
              Finset.sum_le_sum (fun p hp => hgroupNonzero p hp)
        _ = (P.card : ℝ) * (Jset.card : ℝ) * Kext *
              ∑ I ∈ B, ‖b I‖ ^ 2 := by simp [mul_assoc]
    have houterCoeff :
        (P.card : ℝ) * (Jset.card : ℝ) * Kext ≤
          Cpair * (Jset.card : ℝ) * Kext := by
      have hJcardNonneg : 0 ≤ (Jset.card : ℝ) := Nat.cast_nonneg _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hPcardR hJcardNonneg) hKextNonneg
    have hcoeff :
          Cpair * (Jset.card : ℝ) * Kext ≤
            Cpair * Csp * Cext * (N + U ^ 2) * (1 + Real.log N) ^ (S.Sf.card + 1) := by
      calc
        _ ≤ Cpair * (Csp * (1 + Real.log N) ^ S.Sf.card) * Kext := by
          have hCpairNonneg : 0 ≤ Cpair := hCpair.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hJcardR hCpairNonneg) hKextNonneg
        _ = Cpair * Csp * Cext * (N + U ^ 2) *
              (1 + Real.log N) ^ (S.Sf.card + 1) := by
          simpa [Kext, mul_assoc] using
            (conductor_log_coeff_rearrange Cpair Csp Cext (N + U ^ 2)
              (1 + Real.log N) S.Sf.card)
    have hmassNonneg : 0 ≤ ∑ I ∈ B, ‖b I‖ ^ 2 := by positivity
    have hlog := hlogAbsorb N U hN hU
    calc
      _ ≤ ((P.card : ℝ) * (Jset.card : ℝ) * Kext) * ∑ I ∈ B, ‖b I‖ ^ 2 := hraw
      _ ≤ (Cpair * (Jset.card : ℝ) * Kext) * ∑ I ∈ B, ‖b I‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right houterCoeff hmassNonneg
      _ ≤ (Cpair * Csp * Cext * (N + U ^ 2) *
            (1 + Real.log N) ^ (S.Sf.card + 1)) *
            ∑ I ∈ B, ‖b I‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff hmassNonneg
      _ ≤ (Cpair * Csp * Cext * (N + U ^ 2) *
            (Clog * Real.rpow (N * U) ε)) *
            ∑ I ∈ B, ‖b I‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hlog (by positivity)
          · exact hmassNonneg
      _ = Cnz * (N + U ^ 2) * Real.rpow (N * U) ε *
            ∑ I ∈ B, ‖b I‖ ^ 2 := by dsimp [Cnz]; ring
  have hbotMem : (⊥ : Ideal (𝓞 F)) ∈ A := by
    change (⊥ : Ideal (𝓞 F)) ∈
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).toFinset
    apply (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).mem_toFinset.mpr
    simp
  have hbotNot : (⊥ : Ideal (𝓞 F)) ∉ B := by simp [B]
  have hAeq : A = insert ⊥ B := by
    ext I
    by_cases hI : I = ⊥
    · subst I
      simp [B, hbotMem]
    · simp [B, hI]
  have hbotValue (ω : A1.HeckeChar F) : ω.idealValue (⊥ : Ideal (𝓞 F)) = 1 := by
    have hnf : UniqueFactorizationMonoid.normalizedFactors (⊥ : Ideal (𝓞 F)) = 0 := by
      rw [← Ideal.zero_eq_bot, UniqueFactorizationMonoid.normalizedFactors_zero]
    unfold A1.HeckeChar.idealValue
    simp only [hnf, Multiset.map_zero, Multiset.prod_zero]
  have hfullSum (ω : A1.HeckeChar F) :
      (∑ I ∈ A, b I * ω.idealValue I) =
        b ⊥ + ∑ I ∈ B, b I * ω.idealValue I := by
    rw [hAeq, Finset.sum_insert hbotNot]
    simp [hbotValue]
  have htotalMass :
      (∑ I ∈ A, ‖b I‖ ^ 2) = ‖b ⊥‖ ^ 2 + ∑ I ∈ B, ‖b I‖ ^ 2 := by
    rw [hAeq, Finset.sum_insert hbotNot]
  have hfamilyCard : (𝓧.card : ℝ) ≤ Cfam * U ^ 2 := hfamilyCount U hU 𝓧 h𝓧
  have hNUone : 1 ≤ N * U := by nlinarith
  have hpowNU : 1 ≤ Real.rpow (N * U) ε := Real.one_le_rpow hNUone hε.le
  have hbotMassNonneg : 0 ≤ ‖b ⊥‖ ^ 2 := by positivity
  have hsumBot :
      (∑ ω ∈ 𝓧, 2 * ‖b ⊥‖ ^ 2) = 2 * (𝓧.card : ℝ) * ‖b ⊥‖ ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    ring
  have hsumNonzeroScale :
      (∑ ω ∈ 𝓧, 2 * ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2) =
        2 * ∑ ω ∈ 𝓧, ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2 := by
    rw [← Finset.mul_sum]
  have hsplitSquare :
      (∑ ω ∈ 𝓧, ‖∑ I ∈ A, b I * ω.idealValue I‖ ^ 2) ≤
        2 * (𝓧.card : ℝ) * ‖b ⊥‖ ^ 2 +
          2 * ∑ ω ∈ 𝓧, ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2 := by
    calc
      _ = ∑ ω ∈ 𝓧, ‖b ⊥ + ∑ I ∈ B, b I * ω.idealValue I‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [← hfullSum ω]
      _ ≤ ∑ ω ∈ 𝓧,
            (2 * ‖b ⊥‖ ^ 2 +
              2 * ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2) :=
          Finset.sum_le_sum (fun ω hω => conductorNorm_add_sq_le _ _)
      _ = 2 * (𝓧.card : ℝ) * ‖b ⊥‖ ^ 2 +
            2 * ∑ ω ∈ 𝓧, ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2 := by
          rw [Finset.sum_add_distrib, hsumBot, hsumNonzeroScale]
  have hbottomFamily :
      2 * (𝓧.card : ℝ) * ‖b ⊥‖ ^ 2 ≤
        2 * Cfam * U ^ 2 * ‖b ⊥‖ ^ 2 := by
    calc
      _ = 2 * ((𝓧.card : ℝ) * ‖b ⊥‖ ^ 2) := by ring
      _ ≤ 2 * (Cfam * U ^ 2 * ‖b ⊥‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hfamilyCard hbotMassNonneg) (by norm_num)
      _ = 2 * Cfam * U ^ 2 * ‖b ⊥‖ ^ 2 := by ring
  have hnonzeroTwice :
      2 * ∑ ω ∈ 𝓧, ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2 ≤
        2 * Cnz * (N + U ^ 2) * Real.rpow (N * U) ε *
          ∑ I ∈ B, ‖b I‖ ^ 2 := by
    calc
      _ ≤ 2 * (Cnz * (N + U ^ 2) * Real.rpow (N * U) ε *
            ∑ I ∈ B, ‖b I‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hnonzeroBound (by norm_num)
      _ = 2 * Cnz * (N + U ^ 2) * Real.rpow (N * U) ε *
            ∑ I ∈ B, ‖b I‖ ^ 2 := by ring
  have hCfamTwo : 2 * Cfam ≤ C := by dsimp [C]; linarith [hCnz]
  have hCnzTwo : 2 * Cnz ≤ C := by dsimp [C]; linarith [hCfam]
  have hbaseNonneg : 0 ≤ N + U ^ 2 := by positivity
  have hU2le : U ^ 2 ≤ N + U ^ 2 := by
    calc
      U ^ 2 ≤ U ^ 2 + N := le_add_of_nonneg_right hNnonneg
      _ = N + U ^ 2 := by ring
  have hbottomCoeff :
      2 * Cfam * U ^ 2 ≤ C * (N + U ^ 2) * Real.rpow (N * U) ε := by
    calc
      2 * Cfam * U ^ 2 ≤ C * U ^ 2 :=
        mul_le_mul_of_nonneg_right hCfamTwo (sq_nonneg U)
      _ ≤ C * (N + U ^ 2) := mul_le_mul_of_nonneg_left hU2le (by positivity)
      _ = C * (N + U ^ 2) * 1 := by ring
      _ ≤ C * (N + U ^ 2) * Real.rpow (N * U) ε :=
        mul_le_mul_of_nonneg_left hpowNU (mul_nonneg (by positivity) hbaseNonneg)
  have hnonzeroCoeff :
      2 * Cnz * (N + U ^ 2) * Real.rpow (N * U) ε ≤
        C * (N + U ^ 2) * Real.rpow (N * U) ε := by
    calc
      _ = (2 * Cnz) * ((N + U ^ 2) * Real.rpow (N * U) ε) := by ring
      _ ≤ C * ((N + U ^ 2) * Real.rpow (N * U) ε) :=
        mul_le_mul_of_nonneg_right hCnzTwo
          (mul_nonneg hbaseNonneg (Real.rpow_nonneg (by positivity) ε))
      _ = C * (N + U ^ 2) * Real.rpow (N * U) ε := by ring
  calc
    (∑ ω ∈ 𝓧, ‖∑ I ∈ A, b I * ω.idealValue I‖ ^ 2) ≤
        2 * (𝓧.card : ℝ) * ‖b ⊥‖ ^ 2 +
          2 * ∑ ω ∈ 𝓧, ‖∑ I ∈ B, b I * ω.idealValue I‖ ^ 2 := hsplitSquare
    _ ≤ 2 * Cfam * U ^ 2 * ‖b ⊥‖ ^ 2 +
          2 * Cnz * (N + U ^ 2) * Real.rpow (N * U) ε *
            ∑ I ∈ B, ‖b I‖ ^ 2 := add_le_add hbottomFamily hnonzeroTwice
    _ ≤ C * (N + U ^ 2) * Real.rpow (N * U) ε *
          (‖b ⊥‖ ^ 2 + ∑ I ∈ B, ‖b I‖ ^ 2) := by
          calc
            _ ≤ C * (N + U ^ 2) * Real.rpow (N * U) ε * ‖b ⊥‖ ^ 2 +
                  C * (N + U ^ 2) * Real.rpow (N * U) ε *
                    ∑ I ∈ B, ‖b I‖ ^ 2 := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right hbottomCoeff hbotMassNonneg)
                  (mul_le_mul_of_nonneg_right hnonzeroCoeff (by positivity))
            _ = _ := by ring
    _ = C * (N + U ^ 2) * Real.rpow (N * U) ε * ∑ I ∈ A, ‖b I‖ ^ 2 := by
      rw [htotalMass]
    _ = C * (N + U ^ 2) * Real.rpow (N * U) ε *
          ∑ I ∈ conductorIdealCutoff F N, ‖b I‖ ^ 2 := by simp [A]

end ArtinPrimitiveRoots.A2
