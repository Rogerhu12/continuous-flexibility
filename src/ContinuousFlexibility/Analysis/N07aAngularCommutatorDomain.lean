import ContinuousFlexibility.Analysis.N07aSchurCommutator
import ContinuousFlexibility.Analysis.N07aAngularFrequency

/-!
# The actual maximal angular domain of the constructed commutator

The band identity determines a genuine candidate for Λ(Ru).  Its Hilbert
coordinates are square summable because the candidate is already a
member of the prescribed source level.  This proves domain preservation
and the exact commutator identity without assuming either conclusion.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}
  (hV : IsVolumeModel T S K V) (γ w : ℝ)
  (hI : ∀ m, K.left m < K.right m) (b : ℕ)

local instance n07aCommutatorDomainLevelGroup : NormedAddCommGroup (V.level γ w b) :=
  Submodule.normedAddCommGroup _
local instance n07aCommutatorDomainLevelSpace : NormedSpace ℝ (V.level γ w b) :=
  Submodule.normedSpace _
local instance n07aCommutatorDomainLevelInner : InnerProductSpace ℝ (V.level γ w b) :=
  Submodule.innerProductSpace _
local instance n07aCommutatorDomainBandGroup (n : ℕ) :
    NormedAddCommGroup (n07aAngularBandSpace hV γ w hI b n) := Submodule.normedAddCommGroup _
local instance n07aCommutatorDomainBandSpace (n : ℕ) :
    NormedSpace ℝ (n07aAngularBandSpace hV γ w hI b n) := Submodule.normedSpace _
local instance n07aCommutatorDomainBandInner (n : ℕ) :
    InnerProductSpace ℝ (n07aAngularBandSpace hV γ w hI b n) := Submodule.innerProductSpace _
local instance n07aCommutatorDomainLpGroup : NormedAddCommGroup
    (lp (fun n => n07aAngularBandSpace hV γ w hI b n) 2) := lp.normedAddCommGroup
local instance n07aCommutatorDomainLpSpace : NormedSpace ℝ
    (lp (fun n => n07aAngularBandSpace hV γ w hI b n) 2) := lp.instNormedSpace
local instance n07aCommutatorDomainLpInner : InnerProductSpace ℝ
    (lp (fun n => n07aAngularBandSpace hV γ w hI b n) 2) := lp.instInnerProductSpace

theorem n07aAngularLevelBand_hasSum (u : V.level γ w b) :
    HasSum (fun j => n07aAngularLevelBand hV γ w hI b j u) u := by
  have h := n07aAngularHilbertEquiv_symm_hasSum hV γ w hI b
    (n07aAngularHilbertEquiv hV γ w hI b u)
  simpa only [n07aAngularHilbertEquiv_apply_val, LinearIsometryEquiv.symm_apply_apply] using h

theorem n07aAngularCommutator_domain
    (R Q : V.level γ w b →L[ℝ] V.level γ w b)
    (hblock : ∀ l j u,
      n07aAngularLevelBand hV γ w hI b l (Q (n07aAngularLevelBand hV γ w hI b j u)) =
        ((l : ℝ) - j) • n07aAngularLevelBand hV γ w hI b l
          (R (n07aAngularLevelBand hV γ w hI b j u)))
    (u : V.level γ w b)
    (hu : n07aAngularHilbertEquiv hV γ w hI b u ∈ angularFrequencyDomain (𝕜 := ℝ)) :
    n07aAngularHilbertEquiv hV γ w hI b (R u) ∈ angularFrequencyDomain (𝕜 := ℝ) ∧
      n07aAngularLambda hV γ w hI b (R u) = R (n07aAngularLambda hV γ w hI b u) + Q u := by
  let : CompleteSpace (V.level γ w b) := n07aAngularLevelComplete hV γ w b
  let e := n07aAngularHilbertEquiv hV γ w hI b
  let v := R (n07aAngularLambda hV γ w hI b u) + Q u
  have hc (n : ℕ) : e v n = (n : ℝ) • e (R u) n := by
    apply Subtype.ext
    change (e v n).val = (n : ℝ) • (e (R u) n).val
    have hleft : (e v n).val = n07aAngularLevelBand hV γ w hI b n v :=
      n07aAngularHilbertEquiv_apply_val hV γ w hI b v n
    have hright : (e (R u) n).val = n07aAngularLevelBand hV γ w hI b n (R u) :=
      n07aAngularHilbertEquiv_apply_val hV γ w hI b (R u) n
    have hcoord : n07aAngularLevelBand hV γ w hI b n v =
        (n : ℝ) • n07aAngularLevelBand hV γ w hI b n (R u) :=
      n07aCommutator_coordinate_identity
      (fun j => n07aAngularLevelBand hV γ w hI b j) R Q
      (n07aAngularLevelBand_hasSum hV γ w hI b) hblock u
      (n07aAngularLambda hV γ w hI b u)
      (n07aAngularLambda_band hV γ w hI b u hu) n
    exact hleft.trans (hcoord.trans
      (congrArg (fun x : V.level γ w b => (n : ℝ) • x) hright.symm))
  have hdom : e (R u) ∈ angularFrequencyDomain (𝕜 := ℝ) := by
    change Memℓp (fun n : ℕ => (n : ℝ) • e (R u) n) 2
    have he : (fun n : ℕ => (n : ℝ) • e (R u) n) = fun n : ℕ => e v n :=
      funext fun n => (hc n).symm
    rw [he]
    exact lp.memℓp (e v)
  refine ⟨hdom, ?_⟩
  apply e.injective
  apply lp.ext
  funext n
  have hmap : e (n07aAngularLambda hV γ w hI b (R u)) n =
      angularDerivative (𝕜 := ℝ) (e (R u)) n :=
    congrArg (fun x : lp (fun n => n07aAngularBandSpace hV γ w hI b n) 2 => x n)
      (n07aAngularLambda_coordinates hV γ w hI b (R u))
  have hd : angularDerivative (𝕜 := ℝ) (e (R u)) n = (n : ℝ) • e (R u) n := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using angularDerivative_apply (𝕜 := ℝ) hdom n
  exact hmap.trans (hd.trans (hc n).symm)

end ContinuousFlexibility.Statements
