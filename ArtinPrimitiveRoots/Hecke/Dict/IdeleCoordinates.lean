import ArtinPrimitiveRoots.Hecke.Dict.FiniteAdeleIdeal
import TauCeti.NumberTheory.NumberField.Global.Ideles.Basic

/-! Basic placewise coordinates for ideles, adapted from the TauCeti idelic API (Apache-2.0). -/

set_option autoImplicit false

open IsDedekindDomain NumberField
open Classical
open scoped NumberField AdeleRing FiniteAdeleRing

noncomputable section

namespace ArtinPrimitiveRoots.Dictionary

variable {K : Type*} [Field K] [NumberField K]

/-- The finite completion coordinate of an idele as a unit-valued monoid homomorphism. -/
def ideleFiniteCoord (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup (𝓞 K) K →* (v.adicCompletion K)ˣ :=
  Units.map <| (RestrictedProduct.evalMonoidHom _ v).comp
    (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

@[simp]
theorem ideleFiniteCoord_apply (v : HeightOneSpectrum (𝓞 K))
    (x : IdeleGroup (𝓞 K) K) :
    ((ideleFiniteCoord v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ((x : AdeleRing (𝓞 K) K).2 v) := rfl

/-- The infinite completion coordinate of an idele. -/
def ideleInfiniteCoord (w : InfinitePlace K) (x : IdeleGroup (𝓞 K) K) : w.Completion :=
  ((x : AdeleRing (𝓞 K) K).1 w)

/-- The infinite completion coordinate of an idele, as a unit-valued homomorphism. -/
def ideleInfiniteCoordUnit (w : InfinitePlace K) :
    IdeleGroup (𝓞 K) K →* w.Completionˣ :=
  Units.map <| (Pi.evalMonoidHom (fun w : InfinitePlace K => w.Completion) w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

@[simp]
theorem ideleInfiniteCoordUnit_apply (w : InfinitePlace K)
    (x : IdeleGroup (𝓞 K) K) :
    ((ideleInfiniteCoordUnit w x : w.Completionˣ) : w.Completion) =
      ideleInfiniteCoord w x := rfl

@[simp]
theorem ideleInfiniteCoord_mul (w : InfinitePlace K) (x y : IdeleGroup (𝓞 K) K) :
    ideleInfiniteCoord w (x * y) = ideleInfiniteCoord w x * ideleInfiniteCoord w y := rfl

@[simp]
theorem ideleFiniteCoord_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ideleFiniteCoord v (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = u := by
  classical
  apply Units.ext
  exact (FiniteAdeleRing.ofAdicCompletion_apply_coe K v u v).trans
    (Pi.mulSingle_eq_same _ _)

@[simp]
theorem ideleFiniteCoord_ofAdicCompletion_of_ne (v' v : HeightOneSpectrum (𝓞 K))
    (h : v' ≠ v) (u : (v.adicCompletion K)ˣ) :
    ideleFiniteCoord v' (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = 1 := by
  classical
  apply Units.ext
  exact (FiniteAdeleRing.ofAdicCompletion_apply_coe K v u v').trans
    (Pi.mulSingle_eq_of_ne h _)

@[simp]
theorem ideleFiniteCoord_ofCompletion (v : HeightOneSpectrum (𝓞 K))
    (w : InfinitePlace K) (u : w.Completionˣ) :
    ideleFiniteCoord v (IdeleGroup.ofCompletion (𝓞 K) K w u) = 1 := by
  apply Units.ext
  rfl

@[simp]
theorem ideleInfiniteCoordUnit_ofAdicCompletion (w : InfinitePlace K)
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    ideleInfiniteCoordUnit w (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = 1 := by
  apply Units.ext
  rfl

@[simp]
theorem ideleInfiniteCoordUnit_ofCompletion_self (w : InfinitePlace K)
    (u : w.Completionˣ) :
    ideleInfiniteCoordUnit w (IdeleGroup.ofCompletion (𝓞 K) K w u) = u := by
  classical
  apply Units.ext
  exact (InfiniteAdeleRing.ofCompletion_apply w u w).trans
    (Pi.mulSingle_eq_same _ _)

@[simp]
theorem ideleInfiniteCoordUnit_ofCompletion_of_ne (w' w : InfinitePlace K)
    (h : w' ≠ w) (u : w.Completionˣ) :
    ideleInfiniteCoordUnit w' (IdeleGroup.ofCompletion (𝓞 K) K w u) = 1 := by
  classical
  apply Units.ext
  exact (InfiniteAdeleRing.ofCompletion_apply w u w').trans
    (Pi.mulSingle_eq_of_ne h _)

/-- Finite coordinates of the finite-support idele product at a finite set of places. -/
theorem ideleFiniteCoord_finsetProduct (v' : HeightOneSpectrum (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) :
    ideleFiniteCoord v' (∏ v ∈ S, IdeleGroup.ofAdicCompletion (𝓞 K) K v (u v)) =
      if v' ∈ S then u v' else 1 := by
  classical
  rw [map_prod]
  by_cases hv : v' ∈ S
  · rw [if_pos hv, Finset.prod_eq_single_of_mem v' hv]
    · exact ideleFiniteCoord_ofAdicCompletion v' (u v')
    · intro v hvS hne
      exact ideleFiniteCoord_ofAdicCompletion_of_ne v' v (Ne.symm hne) (u v)
  · rw [if_neg hv, Finset.prod_eq_one]
    intro v hvS
    exact ideleFiniteCoord_ofAdicCompletion_of_ne v' v
      (Ne.symm (ne_of_mem_of_not_mem hvS hv)) (u v)

/-- Infinite coordinates of the finite-support idele product at a finite set of places. -/
theorem ideleInfiniteCoordUnit_finsetProduct (w' : InfinitePlace K)
    (S : Finset (InfinitePlace K)) (u : ∀ w : InfinitePlace K, w.Completionˣ) :
    ideleInfiniteCoordUnit w' (∏ w ∈ S, IdeleGroup.ofCompletion (𝓞 K) K w (u w)) =
      if w' ∈ S then u w' else 1 := by
  classical
  rw [map_prod]
  by_cases hw : w' ∈ S
  · rw [if_pos hw, Finset.prod_eq_single_of_mem w' hw]
    · exact ideleInfiniteCoordUnit_ofCompletion_self w' (u w')
    · intro w hwS hne
      exact ideleInfiniteCoordUnit_ofCompletion_of_ne w' w (Ne.symm hne) (u w)
  · rw [if_neg hw, Finset.prod_eq_one]
    intro w hwS
    exact ideleInfiniteCoordUnit_ofCompletion_of_ne w' w
      (Ne.symm (ne_of_mem_of_not_mem hwS hw)) (u w)

@[simp]
theorem ideleInfiniteCoord_unitEmbedding (w : InfinitePlace K) (a : Kˣ) :
    ideleInfiniteCoord w (IdeleGroup.unitEmbedding (𝓞 K) K a) = (a : K) := rfl

end ArtinPrimitiveRoots.Dictionary
