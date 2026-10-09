import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_automorphic
import ArtinPrimitiveRoots.Theta.Proofs.TH_NONZERO.residue_right_of_scalar_invariant
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Arithmetic

set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Rational approximation and the uniform finite level extend archimedean
upper-root invariance to each exterior finite upper root. -/
theorem residue_exterior_upper_invariant_of_arch_invariant
    {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam)
    (harch : ∀ (x : InfinitePlace F → ℂ) (g : P.tc.G),
      C.theta (nInf P x * g) = C.theta g) :
    ∀ (v : FinPlace F), v ∉ S.Sf → ∀ (x : v.adicCompletion F) (g : P.tc.G),
      C.theta (P.emb v ((P.loc v).n (Multiplicative.ofAdd x)) * g) = C.theta g := by
  intro v0 _hv0 x g
  obtain ⟨r, hrg⟩ := P.q_surj g
  have hS : S.Sf ⊆ Fam.T0 := by
    intro v hv
    have h := (Fam.sec 0).sub hv
    rwa [Fam.T0_eq 0] at h
  let Bad : Set (FinPlace F) :=
    {v | ∃ hv : v ∉ S.Sf, P.compF v r ∉ (P.tame v hv).Kmax}
  have hBad : Bad.Finite := P.comp_restricted r
  let T : Finset (FinPlace F) := insert v0 (Fam.T0 ∪ hBad.toFinset)
  let target (v : FinPlace F) : v.adicCompletion F :=
    if h : v = v0 then h.symm ▸ x else 0
  let level (v : FinPlace F) (hv : v ∈ Fam.T0) : ℕ := (Fam.level v hv).choose
  have hlevel (v : FinPlace F) (hv : v ∈ Fam.T0) :
      (P.loc v).m0 ≤ level v hv ∧ ∀ s y, ∀ k ∈ (P.loc v).Kc (level v hv),
        (Fam.sec s).f v (y * k) = (Fam.sec s).f v y := (Fam.level v hv).choose_spec
  have hsmall (v : FinPlace F) : ∃ n : ℕ,
      ∀ η ∈ ball v n, ∀ s y,
        (Fam.sec s).f v (y * ((P.compF v r)⁻¹ *
          (P.loc v).n (Multiplicative.ofAdd η) * P.compF v r)) = (Fam.sec s).f v y := by
    by_cases hv : v ∈ Fam.T0
    · let U : Set (P.loc v).L :=
        {z | (P.compF v r)⁻¹ * z * P.compF v r ∈ (P.loc v).Kc (level v hv)}
      have hUopen : IsOpen U := by
        apply (P.loc v).Kc_open (level v hv) (hlevel v hv).1 |>.preimage
        fun_prop
      have hUone : (1 : (P.loc v).L) ∈ U := by simp [U]
      obtain ⟨n, hn, hsub⟩ := (P.loc v).Kc_nhds U (hUopen.mem_nhds hUone)
      refine ⟨n, ?_⟩
      intro η hη s y
      exact (hlevel v hv).2 s y _ (hsub ((P.loc v).n_Kc n hn η hη))
    · have hvS : v ∉ S.Sf := fun h => hv (hS h)
      let U : Set (P.loc v).L :=
        {z | (P.compF v r)⁻¹ * z * P.compF v r ∈ (P.tame v hvS).Kmax}
      have hUopen : IsOpen U := by
        apply (P.tame v hvS).open_.preimage
        fun_prop
      have hUone : (1 : (P.loc v).L) ∈ U := by simp [U]
      obtain ⟨n, hn, hsub⟩ := (P.loc v).Kc_nhds U (hUopen.mem_nhds hUone)
      refine ⟨n, ?_⟩
      intro η hη s y
      have hvsec : v ∉ (Fam.sec s).T0 := by rw [Fam.T0_eq s]; exact hv
      exact ((Fam.sec s).f_sph v hvsec).2 y _ (hsub ((P.loc v).n_Kc n hn η hη))
  let nBound (v : FinPlace F) := (hsmall v).choose
  obtain ⟨ξ, hξint, hξnear⟩ := th_classical_sInteger_finite_approx T
    (fun v => target v.1) (fun v => nBound v.1)
  have hball (v : FinPlace F) (hv : v ∈ T) :
      ((ξ : v.adicCompletion F) - target v) ∈ ball v (nBound v) := by
    exact (hξnear ⟨v, hv⟩).le
  let u : S.FS := (0, -infEmbA ξ)
  obtain ⟨rA, hqA, hcompFA, hcompCA⟩ := P.nS_components u
  let rN := P.ratRP (upperGL ξ) * rA
  have hqN : P.q rN = nFin P ξ := by
    change P.q (P.ratRP (upperGL ξ) * rA) = _
    rw [map_mul, P.q_ratRP, hqA]
    rfl
  have hcompN (v : FinPlace F) :
      P.compF v rN = (P.loc v).n (Multiplicative.ofAdd (ξ : v.adicCompletion F)) := by
    have hmap : Matrix.GeneralLinearGroup.map
        (algebraMap F (v.adicCompletion F)) (upperGL ξ) =
        upperM (v.adicCompletion F) (algebraMap F (v.adicCompletion F) ξ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperGL, upperM]
    have hA : P.compF v rA = 1 := by
      rw [hcompFA v]
      by_cases hv : v ∈ S.Sf <;> simp [u, hv]
    dsimp only [rN]
    rw [map_mul, P.compF_ratRP, hmap, hA, mul_one, ← (P.loc v).sec_n]
    rfl
  have hcompNC (w : InfinitePlace F) : P.compC w rN = 1 := by
    have hmap : Matrix.GeneralLinearGroup.map w.embedding (upperGL ξ) =
        upperM ℂ (w.embedding ξ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperGL, upperM]
    dsimp only [rN]
    rw [map_mul, P.compC_ratRP, hmap, hcompCA w]
    have hu : u.2 w = -w.embedding ξ := rfl
    rw [← QuotientGroup.mk_mul, hu]
    have hmul : upperM ℂ (w.embedding ξ) * upperM ℂ (-w.embedding ξ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperM, Matrix.mul_apply]
    rw [hmul]
    simp
  let r0 := P.incl v0 ((P.loc v0).n (Multiplicative.ofAdd x))
  let dRP := r0⁻¹ * rN
  let kRP := r⁻¹ * dRP * r
  have hcompD (v : FinPlace F) : P.compF v dRP =
      (P.loc v).n (Multiplicative.ofAdd ((ξ : v.adicCompletion F) - target v)) := by
    dsimp only [dRP]
    rw [map_mul, map_inv, hcompN]
    by_cases hv : v = v0
    · subst v
      rw [show P.compF v0 r0 = (P.loc v0).n (Multiplicative.ofAdd x) by
        exact P.incl_compF v0 _]
      rw [← map_inv, ← map_mul]
      congr 1
      simp [target, sub_eq_add_neg, add_comm]
    · rw [show P.compF v r0 = 1 by exact P.incl_compF_other v0 v (Ne.symm hv) _]
      simp [target, hv]
  have hcompK (v : FinPlace F) : P.compF v kRP =
      (P.compF v r)⁻¹ *
        (P.loc v).n (Multiplicative.ofAdd ((ξ : v.adicCompletion F) - target v)) *
          P.compF v r := by
    simp only [kRP, map_mul, map_inv, hcompD]
  have hcompKC (w : InfinitePlace F) : P.compC w kRP = 1 := by
    simp [kRP, dRP, r0, map_mul, map_inv, P.incl_compC, hcompNC]
  have hlocalFix (v : FinPlace F) (s : ℂ) (y : (P.loc v).L) :
      (Fam.sec s).f v (y * P.compF v kRP) = (Fam.sec s).f v y := by
    rw [hcompK]
    by_cases hv : v ∈ T
    · exact (hsmall v).choose_spec _ (hball v hv) s y
    · have hv0 : v ≠ v0 := by
        intro h
        apply hv
        simp [T, h]
      have hvT : v ∉ Fam.T0 := by
        intro h
        apply hv
        simp [T, h]
      have hvS : v ∉ S.Sf := fun h => hvT (hS h)
      have hrK : P.compF v r ∈ (P.tame v hvS).Kmax := by
        by_contra h
        apply hv
        have hBadmem : v ∈ Bad := ⟨hvS, h⟩
        have hFin : v ∈ hBad.toFinset := hBad.mem_toFinset.mpr hBadmem
        simp [T, hFin]
      have hηint : (ξ : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
        change Valued.v (ξ : v.adicCompletion F) ≤ 1
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        exact hξint v hv
      have hnK := (P.tame v hvS).n_mem (ξ : v.adicCompletion F) hηint
      have hK := (P.tame v hvS).Kmax.mul_mem
        ((P.tame v hvS).Kmax.mul_mem ((P.tame v hvS).Kmax.inv_mem hrK) hnK) hrK
      have hvsec : v ∉ (Fam.sec s).T0 := by rw [Fam.T0_eq s]; exact hvT
      simpa [target, hv0] using ((Fam.sec s).f_sph v hvsec).2 y _ hK
  have hscalar : ∀ s h,
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * P.q kRP) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
    intro s h
    obtain ⟨a, ha⟩ := P.q_surj h
    have hak : P.q (a * kRP) = h * P.q kRP := by simp [ha]
    rw [← hak, ← ha]
    rw [(scalarOf_q P G (Fam.sec s) (a * kRP)).2,
      (scalarOf_q P G (Fam.sec s) a).2]
    congr 1
    · apply finprod_congr
      intro v
      rw [map_mul]
      exact congrArg (G.lam v) (hlocalFix v s (P.compF v a))
    · apply Finset.prod_congr rfl
      intro w hw
      simp [map_mul, hcompKC]
  have hthetaK := residue_right_of_scalar_invariant Fam C (P.q kRP) hscalar
  have hqK : P.q kRP = g⁻¹ *
      (P.emb v0 ((P.loc v0).n (Multiplicative.ofAdd x)))⁻¹ * nFin P ξ * g := by
    simp [kRP, dRP, r0, map_mul, map_inv, P.q_incl, hqN, hrg, mul_assoc]
  have hbase : (P.emb v0 ((P.loc v0).n (Multiplicative.ofAdd x)) * g) * P.q kRP =
      nFin P ξ * g := by
    rw [hqK]
    simp [mul_assoc]
  calc
    C.theta (P.emb v0 ((P.loc v0).n (Multiplicative.ofAdd x)) * g) =
        C.theta ((P.emb v0 ((P.loc v0).n (Multiplicative.ofAdd x)) * g) * P.q kRP) :=
      (hthetaK _).symm
    _ = C.theta (nFin P ξ * g) := congrArg C.theta hbase
    _ = C.theta (P.tc.rat (upperGL ξ) * (nInf P (-infEmbA ξ) * g)) := by
      rw [nFin, mul_assoc]
    _ = C.theta (nInf P (-infEmbA ξ) * g) := residue_automorphic Fam C _ _
    _ = C.theta g := harch _ _

end ArtinPrimitiveRoots.A1.Theta
