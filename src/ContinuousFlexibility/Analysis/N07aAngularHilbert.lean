module

public import ContinuousFlexibility.Analysis.N07aAngularJetBands
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The actual source level as a full Hilbert sum of angular bands

The summands are closed subspaces of the prescribed source level itself.
Their completeness and totality follow from the genuine weak-graph
projection constructed earlier. The resulting equivalence is onto; no
unproved spectral realization property is included in its hypotheses.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}
  (hV : IsVolumeModel T S K V) (γ w : ℝ)
  (hK : ∀ m, K.left m < K.right m) (s : ℕ)

local instance : NormedAddCommGroup (V.level γ w s) := Submodule.normedAddCommGroup _
local instance : NormedSpace ℝ (V.level γ w s) := Submodule.normedSpace _
local instance : InnerProductSpace ℝ (V.level γ w s) := Submodule.innerProductSpace _

/-- The closed actual band, represented by the fixed points of its projection. -/
def n07aAngularBandSpace (n : ℕ) : Submodule ℝ (V.level γ w s) :=
  (n07aAngularLevelBand hV γ w hK s n - ContinuousLinearMap.id ℝ (V.level γ w s)).ker

theorem n07aAngularBandSpace_mem_iff (n : ℕ) (u : V.level γ w s) :
    u ∈ n07aAngularBandSpace hV γ w hK s n ↔
      n07aAngularLevelBand hV γ w hK s n u = u := by
  simp only [n07aAngularBandSpace, LinearMap.mem_ker, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.sub_apply', ContinuousLinearMap.id_apply, sub_eq_zero]

theorem n07aAngularLevelBand_mem (n : ℕ) (u : V.level γ w s) :
    n07aAngularLevelBand hV γ w hK s n u ∈ n07aAngularBandSpace hV γ w hK s n := by
  rw [n07aAngularBandSpace_mem_iff]
  exact n07aAngularLevelBand_idempotent hV γ w hK s n u

theorem n07aAngularBandSpace_isClosed (n : ℕ) :
    IsClosed (n07aAngularBandSpace hV γ w hK s n : Set (V.level γ w s)) :=
  ContinuousLinearMap.isClosed_ker _

include hV in
theorem n07aAngularLevelComplete : CompleteSpace (V.level γ w s) :=
  (hV.2.1 γ w s).completeSpace_coe

local instance (n : ℕ) : NormedAddCommGroup (n07aAngularBandSpace hV γ w hK s n) :=
  Submodule.normedAddCommGroup _

local instance (n : ℕ) : InnerProductSpace ℝ (n07aAngularBandSpace hV γ w hK s n) :=
  Submodule.innerProductSpace _

local instance [CompleteSpace (V.level γ w s)] (n : ℕ) :
    CompleteSpace (n07aAngularBandSpace hV γ w hK s n) :=
  (n07aAngularBandSpace_isClosed hV γ w hK s n).completeSpace_coe

theorem n07aAngularBandSpace_orthogonal :
    OrthogonalFamily ℝ (fun n => n07aAngularBandSpace hV γ w hK s n)
      (fun n => (n07aAngularBandSpace hV γ w hK s n).subtypeₗᵢ) := by
  intro n l hnl u v
  have hu := (n07aAngularBandSpace_mem_iff hV γ w hK s n u.val).mp u.property
  have hv := (n07aAngularBandSpace_mem_iff hV γ w hK s l v.val).mp v.property
  simpa only [hu, hv, Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply] using
    n07aAngularLevelBand_orthogonal hV γ w hK s hnl u.val v.val

theorem n07aAngularBandSpace_total :
    (⨆ n, n07aAngularBandSpace hV γ w hK s n).topologicalClosure = ⊤ := by
  let : CompleteSpace (V.level γ w s) := n07aAngularLevelComplete hV γ w s
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  apply n07aAngularLevelBand_total hV γ w hK s u
  intro n
  have hmem : n07aAngularLevelBand hV γ w hK s n u ∈
      ⨆ l, n07aAngularBandSpace hV γ w hK s l :=
    (le_iSup (fun l => n07aAngularBandSpace hV γ w hK s l) n)
      (n07aAngularLevelBand_mem hV γ w hK s n u)
  have hz := Submodule.inner_right_of_mem_orthogonal hmem hu
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  calc
    inner ℝ (n07aAngularLevelBand hV γ w hK s n u)
        (n07aAngularLevelBand hV γ w hK s n u) =
        inner ℝ (n07aAngularLevelBand hV γ w hK s n u) u := by
      rw [← n07aAngularLevelBand_symmetric,
        n07aAngularLevelBand_idempotent]
    _ = 0 := hz

theorem n07aAngular_isHilbertSum :
    letI : CompleteSpace (V.level γ w s) := n07aAngularLevelComplete hV γ w s
    IsHilbertSum ℝ (fun n => n07aAngularBandSpace hV γ w hK s n)
      (fun n => (n07aAngularBandSpace hV γ w hK s n).subtypeₗᵢ) := by
  let : CompleteSpace (V.level γ w s) := n07aAngularLevelComplete hV γ w s
  exact IsHilbertSum.mkInternal _ (n07aAngularBandSpace_orthogonal hV γ w hK s)
    (n07aAngularBandSpace_total hV γ w hK s).ge

/-- Onto isometric coordinates of the prescribed source level in its real bands. -/
def n07aAngularHilbertEquiv : V.level γ w s ≃ₗᵢ[ℝ]
    lp (fun n => n07aAngularBandSpace hV γ w hK s n) 2 := by
  letI : CompleteSpace (V.level γ w s) := n07aAngularLevelComplete hV γ w s
  exact (n07aAngular_isHilbertSum hV γ w hK s).linearIsometryEquiv

theorem n07aAngularHilbertEquiv_symm_hasSum
    (v : lp (fun n => n07aAngularBandSpace hV γ w hK s n) 2) :
    HasSum (fun n => (v n).val) ((n07aAngularHilbertEquiv hV γ w hK s).symm v) := by
  let : CompleteSpace (V.level γ w s) := n07aAngularLevelComplete hV γ w s
  simpa only [n07aAngularHilbertEquiv, Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply] using
    (n07aAngular_isHilbertSum hV γ w hK s).hasSum_linearIsometryEquiv_symm v

theorem n07aAngularLevelBand_band (n l : ℕ)
    (v : n07aAngularBandSpace hV γ w hK s l) :
    n07aAngularLevelBand hV γ w hK s n v.val = if n = l then v.val else 0 := by
  have hv := (n07aAngularBandSpace_mem_iff hV γ w hK s l v.val).mp v.property
  by_cases h : n = l
  · subst n
    simpa only [ite_true] using hv
  · rw [ite_eq_right_iff.mpr (fun h' => (h h').elim), ← hv]
    exact n07aAngularLevelBand_comp_eq_zero hV γ w hK s h v.val

/-- Each Hilbert-sum coordinate is exactly the actual weak-graph projection. -/
theorem n07aAngularHilbertEquiv_apply_val (u : V.level γ w s) (n : ℕ) :
    (n07aAngularHilbertEquiv hV γ w hK s u n).val =
      n07aAngularLevelBand hV γ w hK s n u := by
  classical
  let v := n07aAngularHilbertEquiv hV γ w hK s u
  have hs := (n07aAngularHilbertEquiv_symm_hasSum hV γ w hK s v).map
    (n07aAngularLevelBand hV γ w hK s n) (n07aAngularLevelBand hV γ w hK s n).continuous
  have hs' : HasSum (fun l => if l = n then (v n).val else 0)
      (n07aAngularLevelBand hV γ w hK s n u) := by
    convert hs using 1
    · funext l
      rw [Function.comp_apply, n07aAngularLevelBand_band]
      by_cases h : l = n
      · subst l
        simp only [ite_true]
      · simp only [h, Ne.symm h, ite_false]
    · rw [LinearIsometryEquiv.symm_apply_apply]
  exact (hasSum_ite_eq n (v n).val).unique hs'

end ContinuousFlexibility.Statements
