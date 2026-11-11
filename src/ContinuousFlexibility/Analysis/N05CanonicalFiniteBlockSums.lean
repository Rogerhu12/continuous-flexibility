import ContinuousFlexibility.Analysis.N05CanonicalInverseLinearity
import ContinuousFlexibility.Analysis.N05CanonicalInverseBlock
import ContinuousFlexibility.Analysis.N05CanonicalFiniteApproximation

/-!
# Finite block sums of the same global inverse

The actual finite-cell truncations remain in the source volume graph.
Linearity of the already constructed restriction of the fixed global map
therefore identifies each finite block sum with its literal inverse value.
Continuity of that same restriction identifies the coordinate limits.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter
open scoped BigOperators Topology

theorem n05CanonicalVolumeModel_actual {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (S : PhysicalSpacesData) (K : CanonicalData S) :
    IsVolumeModel T S K (n05CanonicalVolumeModel T S K) := by
  apply n05CanonicalVolumeModel_isVolumeModel T S K
  · intro m
    exact zero_lt_one.trans_le
      (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 m)).2.2.2
  · intro m
    exact (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 m)).2.1

theorem n05CanonicalFiniteTruncate_sum_singletons (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (q : Finset ℕ)
    (v : n05CanonicalClosedSubmodule S K s) :
    n05CanonicalFiniteTruncate S K s q v =
      ∑ m ∈ q, n05CanonicalFiniteTruncate S K s {m} v := by
  apply Subtype.ext
  change n05CanonicalFiniteTruncateRaw S K s q v.val =
    (n05CanonicalClosedSubmodule S K s).subtypeL
      (∑ m ∈ q, n05CanonicalFiniteTruncate S K s {m} v)
  rw [n05CanonicalFiniteTruncateRaw_eq_sum]
  simp only [map_sum, Submodule.subtypeL_apply]
  apply Finset.sum_congr rfl
  intro m hm
  change lp.single 2 m (v.val m) = n05CanonicalFiniteTruncateRaw S K s {m} v.val
  rw [n05CanonicalFiniteTruncateRaw_eq_sum, Finset.sum_singleton]

theorem n05CanonicalFiniteTruncate_forget_singleton (T : MaterialData)
    (S : PhysicalSpacesData) (K : CanonicalData S) (γ t : ℝ) (s m : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t s) :
    (n05CanonicalVolumeModel T S K).forget γ t s
        (n05CanonicalFiniteTruncate S K s {m} v) =
      Pi.single m (n05CanonicalSampleWeight T S K γ t m • v.val m 0) := by
  classical
  funext k
  rw [n05CanonicalVolumeModel_forget, n05CanonicalFiniteTruncate_apply]
  change n05CanonicalSampleWeight T S K γ t k •
    (if k ∈ ({m} : Finset ℕ) then v.val k 0 else 0) = _
  by_cases hkm : k = m
  · subst k
    simp only [Finset.mem_singleton, eq_self_iff_true, ite_true, Pi.single_eq_same]
  · simp only [Finset.mem_singleton, hkm, ite_false, Pi.single_eq_of_ne hkm, smul_zero]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  {γw γ M0 M1 : ℝ} (hγw : 0 < γw) (hgap : γw < γ)
  {G : RadialSource → RadialUnknown} (hG : ReferenceInverseProperties D γw M0 M1 G)

include hD hT hS h hcoordinates hγw hgap hG

/-- The finite sum is an exact equality of genuine canonical L² classes.
Each summand uses the same literal global map on its actual single source. -/
theorem n05CanonicalGlobalInverse_finite_block_sum (t : ℝ) (s : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t s) (q : Finset ℕ) (k : ℕ) :
    (n05CanonicalGlobalInverse D S C K G
      ((n05CanonicalVolumeModel T S K).forget γ t s
        (n05CanonicalFiniteTruncate S K s q v))).1 k =
      ∑ m ∈ q, n05CanonicalInverseBlock D S C K G k m
        (n05CanonicalSampleWeight T S K γ t m • v.val m 0) := by
  let J := n05CanonicalInverseCLM hD hT hS h hcoordinates hγw hG
    (n05CanonicalVolumeModel_actual hD.1 hT S K) hgap t s
  let P := (lp.evalCLM ℝ (fun j => CanonicalL2 S K j) 2 k).comp
    ((ContinuousLinearMap.fst ℝ (CanonicalL2Sequence S K) (ℝ × ℝ × ℝ)).comp J)
  have hP (w : (n05CanonicalVolumeModel T S K).level γ t s) :
      P w = (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t s w)).1 k := by
    simp only [P, J, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      lp.evalCLM, LinearMap.mkContinuous_apply, lp.evalₗ_apply, n05CanonicalInverseCLM_apply]
  have he := map_sum P (fun m => n05CanonicalFiniteTruncate S K s {m} v) q
  rw [← n05CanonicalFiniteTruncate_sum_singletons] at he
  simpa only [hP, n05CanonicalFiniteTruncate_forget_singleton,
    n05CanonicalInverseBlock] using he

/-- Finite block sums converge to the coordinate of the already fixed
global inverse, by its actual continuous restriction on this source level. -/
theorem n05CanonicalGlobalInverse_finite_coordinate_tendsto (t : ℝ) (s : ℕ)
    (v : (n05CanonicalVolumeModel T S K).level γ t s) (k : ℕ) :
    Tendsto (fun q : Finset ℕ =>
      (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t s
          (n05CanonicalFiniteTruncate S K s q v))).1 k) atTop
      (𝓝 ((n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t s v)).1 k)) := by
  let J := n05CanonicalInverseCLM hD hT hS h hcoordinates hγw hG
    (n05CanonicalVolumeModel_actual hD.1 hT S K) hgap t s
  let P := (lp.evalCLM ℝ (fun j => CanonicalL2 S K j) 2 k).comp
    ((ContinuousLinearMap.fst ℝ (CanonicalL2Sequence S K) (ℝ × ℝ × ℝ)).comp J)
  have hP (w : (n05CanonicalVolumeModel T S K).level γ t s) :
      P w = (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t s w)).1 k := by
    simp only [P, J, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      lp.evalCLM, LinearMap.mkContinuous_apply, lp.evalₗ_apply, n05CanonicalInverseCLM_apply]
  have ht := P.continuous.tendsto v |>.comp
    (n05CanonicalFiniteTruncate_tendsto S K s v)
  change Tendsto (fun q : Finset ℕ => P (n05CanonicalFiniteTruncate S K s q v))
    atTop (𝓝 (P v)) at ht
  simpa only [hP] using ht

end ContinuousFlexibility.Statements
