import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.WvAll_properties
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_factor_step
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_argument_decomposition
import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.thetaWhit_tail_invariance

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem thetaWhit_residue_ne_zero_of_valuation_one (v : FinPlace F) (x : F)
    (hxval : HeightOneSpectrum.valuation F v x = 1) : residue v x ≠ 0 := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hxle : HeightOneSpectrum.valuation F v x ≤ 1 := by rw [hxval]
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x hxle
  let hrep : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 :=
    ⟨(a, b), b.property, hab⟩
  unfold residue
  rw [dif_pos hrep]
  have hchosen := hrep.choose_spec
  have hbval' : HeightOneSpectrum.valuation F v
      (algebraMap (𝓞 F) F hrep.choose.2) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := hrep.choose.2)).2 hchosen.1
  have haval' : HeightOneSpectrum.valuation F v
      (algebraMap (𝓞 F) F hrep.choose.1) = 1 := by
    have h := congrArg (HeightOneSpectrum.valuation F v) hchosen.2
    simpa only [map_mul, hxval, hbval', one_mul] using h.symm
  have ha' : hrep.choose.1 ∉ v.asIdeal :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := hrep.choose.1)).mp haval'
  apply mul_ne_zero
  · intro hzero
    exact ha' (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  · apply inv_ne_zero
    intro hzero
    exact hchosen.1 (Ideal.Quotient.eq_zero_iff_mem.mp hzero)

private theorem thetaWhit_toLoc_isLocUnit_of_valuation_one (v : FinPlace F) (x : Fˣ)
    (hx : HeightOneSpectrum.valuation F v (x : F) = 1) : IsLocUnit v (toLoc v x) := by
  have hval : Valued.v ((toLoc v x : v.adicCompletion F) : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hx]
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hval.le
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one, le_refl]

/-- Iterate the one-place factorization over an exterior support enlargement and convert
the remaining finite product to the frozen dependent finprod.
Uses `WvAll_properties`, `thetaWhit_factor_step`, `thetaWhit_argument_decomposition`,
and `thetaWhit_tail_invariance`; feeds frozen `thetaWhit_factor`. -/
theorem thetaWhit_factor_iteration {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ) (hT : Fam.T0 = S.Sf)
    (C : ContinuedEis Fam) (ν : Fˣ) (ε : Bool) (gS : P.tc.G) (hgS : gS ∈ P.tc.GS)
    (T : Finset (FinPlace F)) (hT' : ∀ v ∈ T, v ∉ S.Sf) (g : FinPlace F → P.tc.G)
    (hg : ∀ v ∈ T, g v ∈ P.tc.Gloc v) :
    thetaWhit C (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS * (T.toList.map g).prod) =
    thetaWhit C (P.tc.aS (S.diagU ν) * (if ε then P.tc.wS else 1) * gS) *
        (∏ v ∈ T, WvAll P G μ v (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)) *
        ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T), WvAll P G μ v (P.tc.a v (toLoc v ν)) := by
  classical
  let hνsupp := finitePlace_mk_hasFiniteMulSupport (x := (ν : F)) (Units.ne_zero ν)
  let V : Finset (FinPlace F) := hνsupp.toFinset
  let U : Finset (FinPlace F) := T ∪ (V \ S.Sf)
  let base : P.tc.G := P.tc.aS (S.diagU ν) * (if ε then P.tc.wS else 1) * gS
  let localArg : FinPlace F → P.tc.G := thetaWhit_localArgument P ν ε T g
  let localW : FinPlace F → ℂ := fun v => WvAll P G μ v (localArg v)
  have hval_out : ∀ v, v ∉ V → HeightOneSpectrum.valuation F v (ν : F) = 1 := by
    intro v hv
    have hvnorm : (FinitePlace.mk v) (ν : F) = 1 := by
      by_contra hne
      apply hv
      exact hνsupp.mem_toFinset.mpr (by simpa only [Function.mem_mulSupport] using hne)
    have hnorm : ‖FinitePlace.embedding v (ν : F)‖ = 1 := by
      simpa only [FinitePlace.mk_apply] using hvnorm
    have hnn : WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
        (HeightOneSpectrum.valuation F v (ν : F)) = 1 := by
      apply NNReal.coe_injective
      simpa only [FinitePlace.norm_embedding', NNReal.coe_one] using hnorm
    have hq : (Ideal.absNorm v.asIdeal : NNReal) ≠ 1 := by
      intro h
      have hn : Ideal.absNorm v.asIdeal = 1 := by exact_mod_cast h
      have hlt := HeightOneSpectrum.one_lt_absNorm v
      omega
    exact (WithZeroMulInt.toNNReal_eq_one_iff _
      (HeightOneSpectrum.absNorm_ne_zero v) hq).mp hnn
  have hTU : T ⊆ U := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inl hv)
  have hU : ∀ v ∈ U, v ∉ S.Sf := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvT | hvV
    · exact hT' v hvT
    · exact (Finset.mem_sdiff.mp hvV).2
  have hν : ∀ v : FinPlace F, v ∉ S.Sf → v ∉ U →
      residue v (ν : F) ≠ 0 ∧ residue v ((ν⁻¹ : Fˣ) : F) ≠ 0 := by
    intro v hvS hvU
    have hvV : v ∉ V := by
      intro hvV
      apply hvU
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hvV, hvS⟩))
    have hνval := hval_out v hvV
    have hνival : HeightOneSpectrum.valuation F v ((ν⁻¹ : Fˣ) : F) = 1 := by
      simpa only [Units.val_inv_eq_inv_val, map_inv₀, hνval, inv_one]
    exact ⟨thetaWhit_residue_ne_zero_of_valuation_one v _ hνval,
      thetaWhit_residue_ne_zero_of_valuation_one v _ hνival⟩
  have hbase : base ∈ P.tc.GS := by
    dsimp [base]
    apply P.tc.GS.mul_mem
    · apply P.tc.GS.mul_mem
      · exact P.tc.aS_mem (S.diagU ν)
      · by_cases hε : ε <;> simp [hε, P.tc.wS_mem]
    · exact hgS
  have hQmem : ∀ v ∈ U, localArg v ∈ P.tc.Gloc v := by
    intro v hv
    dsimp [localArg, thetaWhit_localArgument]
    apply P.tc.Gloc v |>.mul_mem
    · apply P.tc.Gloc v |>.mul_mem
      · exact P.tc.a_mem v (toLoc v ν)
      · by_cases hε : ε <;> simp [hε, P.tc.w_mem]
    · split_ifs with hTg
      · exact hg v hTg
      · exact P.tc.Gloc v |>.one_mem
  obtain ⟨kTail, _, _, hdecomp, hfixTail⟩ :=
    thetaWhit_argument_decomposition Fam hT ν ε gS hgS T U hTU hU hν g hg
  have hfix := thetaWhit_tail_invariance Fam C kTail hfixTail
  have hcommList : ∀ (v : FinPlace F) (a : P.tc.G), a ∈ P.tc.Gloc v →
      ∀ l : List (FinPlace F), (∀ u ∈ l, u ∈ U) → (∀ u ∈ l, u ≠ v) →
      a * (l.map localArg).prod = (l.map localArg).prod * a := by
    intro v a ha l
    induction l with
    | nil => intro _ _; simp
    | cons u l ih =>
      intro hmem hne
      have huU : u ∈ U := hmem u (by simp)
      have htailmem : ∀ x ∈ l, x ∈ U := by
        intro x hx
        exact hmem x (by simp [hx])
      have htailne : ∀ x ∈ l, x ≠ v := by
        intro x hx
        exact hne x (by simp [hx])
      have huv : v ≠ u := by
        intro h
        exact (hne u (by simp)) h.symm
      have hcomm := P.tc.comm_loc v u huv a ha (localArg u) (hQmem u huU)
      have htail := ih htailmem htailne
      simp only [List.map_cons, List.prod_cons]
      calc
        a * (localArg u * (l.map localArg).prod) =
            (a * localArg u) * (l.map localArg).prod := by rw [mul_assoc]
        _ = (localArg u * a) * (l.map localArg).prod := by rw [hcomm]
        _ = localArg u * (a * (l.map localArg).prod) := by rw [← mul_assoc]
        _ = localArg u * ((l.map localArg).prod * a) := by rw [htail]
        _ = (localArg u * (l.map localArg).prod) * a := by rw [mul_assoc]
  have hfactorList : ∀ l : List (FinPlace F), l.Nodup →
      (∀ v ∈ l, v ∈ U) →
      thetaWhit C (base * (l.map localArg).prod) =
        thetaWhit C base * (l.map localW).prod := by
    intro l
    induction l with
    | nil => intro _ _; simp
    | cons v l ih =>
      intro hnodup hmem
      rcases List.nodup_cons.mp hnodup with ⟨hvnot, hnodupTail⟩
      have hvU : v ∈ U := hmem v (by simp)
      have htailmem : ∀ u ∈ l, u ∈ U := by
        intro u hu
        exact hmem u (by simp [hu])
      have hvNotTail : ∀ u ∈ l, u ≠ v := by
        intro u hu huv
        apply hvnot
        simpa [huv] using hu
      have htailComm := hcommList v (localArg v) (hQmem v hvU) l htailmem hvNotTail
      have hRange : localArg v ∈ (P.emb v).range := by
        rw [P.emb_Gloc v (hU v hvU)]
        exact hQmem v hvU
      obtain ⟨kv, hkv⟩ := hRange
      have hX : ∀ y : (P.loc v).L,
          (base * (l.map localArg).prod) * P.emb v y =
            P.emb v y * (base * (l.map localArg).prod) := by
        intro y
        have hEmb : P.emb v y ∈ P.tc.Gloc v := by
          rw [← P.emb_Gloc v (hU v hvU)]
          exact ⟨y, rfl⟩
        have htail := hcommList v (P.emb v y) hEmb l htailmem hvNotTail
        have hbaseComm : base * P.emb v y = P.emb v y * base :=
          (P.tc.comm_S v (hU v hvU) (P.emb v y) hEmb base hbase).symm
        calc
          (base * (l.map localArg).prod) * P.emb v y =
              base * ((l.map localArg).prod * P.emb v y) := by rw [mul_assoc]
          _ = base * (P.emb v y * (l.map localArg).prod) := by rw [htail]
          _ = (base * P.emb v y) * (l.map localArg).prod := by rw [← mul_assoc]
          _ = (P.emb v y * base) * (l.map localArg).prod := by rw [hbaseComm]
          _ = P.emb v y * (base * (l.map localArg).prod) := by rw [mul_assoc]
      have hprod : base * (localArg v * (l.map localArg).prod) =
          (base * (l.map localArg).prod) * localArg v := by
        calc
          base * (localArg v * (l.map localArg).prod) =
              base * ((l.map localArg).prod * localArg v) := by rw [htailComm]
          _ = (base * (l.map localArg).prod) * localArg v := by rw [← mul_assoc]
      calc
        thetaWhit C (base * ((v :: l).map localArg).prod) =
            thetaWhit C ((base * (l.map localArg).prod) * P.emb v kv) := by
              rw [List.map_cons, List.prod_cons, hprod, hkv]
        _ = thetaWhit C (base * (l.map localArg).prod) *
              WvAll P G μ v (P.emb v kv) :=
            thetaWhit_factor_step Fam hT C v (hU v hvU)
              (base * (l.map localArg).prod) hX kv
        _ = thetaWhit C base * (l.map localW).prod * localW v := by
              rw [ih hnodupTail htailmem]
              simp [localW, hkv]
        _ = thetaWhit C base * ((v :: l).map localW).prod := by
              simp only [List.map_cons, List.prod_cons]
              ring
  have hfactorU : thetaWhit C (base * (U.toList.map localArg).prod) =
      thetaWhit C base * (U.toList.map localW).prod :=
    hfactorList U.toList (Finset.nodup_toList U)
      (by intro v hv; exact Finset.mem_toList.mp hv)
  have hWprops := WvAll_properties P G μ
  have hWright : ∀ v, v ∉ S.Sf → v ∉ T →
      localW v = WvAll P G μ v (P.tc.a v (toLoc v ν)) := by
    intro v hvS hvT
    have hcompact : (if ε then P.tc.w v else 1) ∈ P.tc.Kext := by
      by_cases hε : ε
      · simpa [hε] using P.tc.w_Kext v hvS
      · simp [hε]
    have hgloc : (if ε then P.tc.w v else 1) ∈ P.tc.Gloc v := by
      by_cases hε : ε
      · simpa [hε] using P.tc.w_mem v
      · simp [hε]
    have hright := hWprops.2.2.1 v hvS (P.tc.a v (toLoc v ν))
      (if ε then P.tc.w v else 1) hcompact hgloc
    simpa [localW, localArg, thetaWhit_localArgument, hvT] using hright
  have hWbaseUnit : ∀ v, v ∉ S.Sf → v ∉ U →
      WvAll P G μ v (P.tc.a v (toLoc v ν)) = 1 := by
    intro v hvS hvU
    have hvV : v ∉ V := by
      intro hvV
      exact hvU (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hvV, hvS⟩)))
    have hval := hval_out v hvV
    have hloc : IsLocUnit v (toLoc v ν) :=
      thetaWhit_toLoc_isLocUnit_of_valuation_one v ν hval
    have hlocalval : Valued.v ((toLoc v ν : v.adicCompletion F) : v.adicCompletion F) = 1 := by
      change Valued.v (algebraMap F (v.adicCompletion F) (ν : F)) = 1
      simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hval]
    have hlocalval_ne : Valued.v ((toLoc v ν : v.adicCompletion F) : v.adicCompletion F) ≠ 0 := by
      rw [hlocalval]
      exact one_ne_zero
    have hord : ordv v (toLoc v ν) = 0 := by
      have hvalExp : Valued.v ((toLoc v ν : v.adicCompletion F) : v.adicCompletion F) =
          WithZero.exp (-ordv v (toLoc v ν)) := by
        rw [← WithZero.exp_log hlocalval_ne]
        simp [ordv, WithZero.toAdd_unzero_eq_log hlocalval_ne]
      have harg : -ordv v (toLoc v ν) = 0 := by
        apply WithZero.exp_injective
        calc
          WithZero.exp (-ordv v (toLoc v ν)) =
              Valued.v ((toLoc v ν : v.adicCompletion F) : v.adicCompletion F) := hvalExp.symm
          _ = 1 := hlocalval
          _ = WithZero.exp (0 : ℤ) := by simp
      exact neg_eq_zero.mp harg
    have hunitPart : unitPart v (toLoc v ν) = toLoc v ν := by
      have h := unitPart_factor v (toLoc v ν)
      rw [hord] at h
      simpa using h
    have htable := hWprops.2.2.2 v hvS 0 (toLoc v ν) hloc.1 hloc.2
    simpa [hord, hunitPart, sphericalTable] using htable
  let factorT : ℂ :=
    ∏ v ∈ T, WvAll P G μ v
      (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)
  let factorTail : ℂ := ∏ v ∈ U \ T, WvAll P G μ v (P.tc.a v (toLoc v ν))
  have hleft : thetaWhit C
      (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS *
        (T.toList.map g).prod) = thetaWhit C (base * (U.toList.map localArg).prod) := by
    calc
      thetaWhit C
          (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS *
            (T.toList.map g).prod) =
          thetaWhit C ((base * (U.toList.map localArg).prod) * kTail) := by
            rw [hdecomp]
      _ = thetaWhit C (base * (U.toList.map localArg).prod) := hfix _
  have hprodU : (U.toList.map localW).prod = factorT * factorTail := by
    rw [Finset.prod_map_toList]
    have hsplit : (∏ v ∈ U \ T, localW v) * (∏ v ∈ T, localW v) =
        ∏ v ∈ U, localW v := Finset.prod_sdiff hTU
    calc
      (∏ v ∈ U, localW v) =
          (∏ v ∈ U \ T, localW v) * (∏ v ∈ T, localW v) := hsplit.symm
      _ = (∏ v ∈ T, localW v) * (∏ v ∈ U \ T, localW v) := mul_comm _ _
      _ = (∏ v ∈ T, WvAll P G μ v
            (P.tc.a v (toLoc v ν) * (if ε then P.tc.w v else 1) * g v)) *
          (∏ v ∈ U \ T, WvAll P G μ v (P.tc.a v (toLoc v ν))) := by
            congr 1
            · apply Finset.prod_congr rfl
              intro v hv
              simp [localW, localArg, thetaWhit_localArgument, hv]
            · apply Finset.prod_congr rfl
              intro v hv
              exact hWright v (hU v (Finset.mem_sdiff.mp hv).1)
                (Finset.mem_sdiff.mp hv).2
      _ = factorT * factorTail := by rfl
  have htailFinprod :
      (∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T),
        WvAll P G μ v (P.tc.a v (toLoc v ν))) =
      ∏ v ∈ U \ T, WvAll P G μ v (P.tc.a v (toLoc v ν)) := by
    apply finprod_cond_eq_prod_of_cond_iff
    intro v hvne
    constructor
    · intro hv
      rcases hv with ⟨hvS, hvT⟩
      have hvU : v ∈ U := by
        by_contra hnot
        exact hvne (hWbaseUnit v hvS hnot)
      exact Finset.mem_sdiff.mpr ⟨hvU, hvT⟩
    · intro hv
      rcases Finset.mem_sdiff.mp hv with ⟨hvU, hvT⟩
      exact ⟨hU v hvU, hvT⟩
  calc
    thetaWhit C (P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS *
        (T.toList.map g).prod) = thetaWhit C (base * (U.toList.map localArg).prod) := hleft
    _ = thetaWhit C base * (U.toList.map localW).prod := hfactorU
    _ = thetaWhit C base * (factorT * factorTail) := by rw [hprodU]
    _ = (thetaWhit C base * factorT) *
        ∏ᶠ (v : FinPlace F) (_ : v ∉ S.Sf ∧ v ∉ T),
          WvAll P G μ v (P.tc.a v (toLoc v ν)) := by
            calc
              thetaWhit C base * (factorT * factorTail) =
                  (thetaWhit C base * factorT) * factorTail := by ring
              _ = (thetaWhit C base * factorT) *
                  (∏ v ∈ U \ T, WvAll P G μ v (P.tc.a v (toLoc v ν))) := by rfl
              _ = _ := by rw [← htailFinprod]
    _ = _ := rfl

end ArtinPrimitiveRoots.A1.Theta
