import ContinuousFlexibility.Analysis.N08CircleDerivative
import ContinuousFlexibility.Analysis.N08FlowLocality
import ContinuousFlexibility.Analysis.N08ControlBasis
import ContinuousFlexibility.Analysis.N08ControlDiagonal
import ContinuousFlexibility.Analysis.N08ProfilePointwise

/-!
# The actual diagonal control mean derivative

The diagonal is evaluated on the actual unit control basis.  Component
locality of the ordinary flow proves that every direction with zero
control mean at `m` has zero derivative in that output coordinate.
Linearity then gives the exact diagonal formula for every direction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

def n08ControlMeanCoordinate (S : PhysicalSpacesData) (m : ℕ) : CircleSpace S →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m).comp (n08ControlRestriction S)

theorem n08ControlMeanCoordinate_apply (S : PhysicalSpacesData) (m : ℕ) (u : CircleSpace S) :
    n08ControlMeanCoordinate S m u = n08ControlRestriction S u m := by
  calc
    _ = (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 m) (n08ControlRestriction S u) :=
      ContinuousLinearMap.comp_apply _ _ _
    _ = _ := lp.evalₗ_apply (fun _ : ℕ => ℝ) 2 m (n08ControlRestriction S u)

theorem n08_materialSample_H_pos (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (m : ℕ) : 0 < T.H (T.sample m) :=
  (hT.2.1 _ (materialSample_mem_radialCore hT hRef.choose_spec.2.1 m)).2.1

private theorem n08CircleResidual_mean_zero_hasLineDerivAt
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ)
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (u : CircleSpace S) (hu : n08ControlMeanCoordinate S m u = 0) :
    HasProjectiveLineDerivAt
      (fun x => n08ControlMeanCoordinate S m (n08CircleResidual hS hR (x, z.2)).val)
      0 z.1 (0, (0, (u, 0))) := by
  let v : AnnularState S := (0, (0, (u, 0)))
  have hmean : stateKappa S v m = 0 := by
    rw [n08ControlMeanCoordinate_apply, n08ControlRestriction_apply hS] at hu
    exact (mul_eq_zero.mp hu).resolve_left
      (Real.rpow_pos_of_pos (n08_materialSample_H_pos hT hN.1.1 m) _).ne'
  have hc : Continuous (fun t : ℝ => (n08_stateProjection hS (z.1 + t • v), z.2)) :=
    ((n08_stateProjection hS).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).prodMk continuous_const
  have ht : Tendsto (fun t : ℝ => (n08_stateProjection hS (z.1 + t • v), z.2))
      (𝓝[≠] (0 : ℝ)) (𝓝 (n08_stateProjection hS z.1, z.2)) := by
    simpa only [zero_smul, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev := ht.eventually ((n08_isOpen_stateNeighborhood S C base ε).mem_nhds hz)
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
  simp only [zero_add, zero_smul, add_zero]
  apply (tendsto_const_nhds (x := (0 : ℝ)) :
    Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] (0 : ℝ)) (𝓝 0)).congr'
  filter_upwards [hev] with t ht
  have hheight : (n08_stateProjection hS (z.1 + t • v)).1 =
      (n08_stateProjection hS z.1).1 := by
    rw [map_add, map_smul]
    simp only [v, n08_stateProjection_kappaDirection, Prod.fst_add, Prod.fst_smul,
      smul_zero, add_zero]
  have hν : (n08_stateProjection hS (z.1 + t • v)).2.1 =
      (n08_stateProjection hS z.1).2.1 := by
    rw [map_add, map_smul]
    simp only [v, n08_stateProjection_kappaDirection, Prod.snd_add, Prod.snd_smul,
      Prod.fst_add, Prod.fst_smul, smul_zero, add_zero]
  have hκ : stateKappa S (n08_stateProjection hS (z.1 + t • v)) m =
      stateKappa S (n08_stateProjection hS z.1) m := by
    rw [n08_stateKappa_projection, n08_stateKappa_projection, n08_stateKappa_add hS,
      n08_stateKappa_smul hS, hmean, mul_zero, add_zero]
  have hchartValue : (n08_stateProjection hS (z.1 + t • v)).2.2.2 =
      (n08_stateProjection hS z.1).2.2.2 := by
    rw [map_add, map_smul]
    simp only [v, n08_stateProjection_kappaDirection, Prod.snd_add, Prod.snd_smul,
      smul_zero, add_zero]
  have hchart : stateLeftChart S (n08_stateProjection hS (z.1 + t • v)) m =
      stateLeftChart S (n08_stateProjection hS z.1) m := by
    funext θ
    simp only [stateLeftChart, hchartValue]
  have heq : n08ControlMeanCoordinate S m (n08CircleResidual hS hR (z.1 + t • v, z.2)).val =
      n08ControlMeanCoordinate S m (n08CircleResidual hS hR z).val := by
    rw [n08ControlMeanCoordinate_apply, n08ControlMeanCoordinate_apply,
      n08ControlRestriction_apply hS, n08ControlRestriction_apply hS,
      n08CircleResidual_projected_coe hS hR ht, n08CircleResidual_projected_coe hS hR hz]
    congr 1
    apply congrArg angularMean
    funext θ
    exact n08_returnResidual_component_eq hT hS hN hR ht hz
      (n08_stateProjection_mem hS _) (n08_stateProjection_mem hS _) hheight hν hκ hchart θ
  rw [heq, sub_self, smul_zero]

theorem n08CircleColumn_mean_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (u : CircleSpace S) (hu : n08ControlMeanCoordinate S m u = 0) :
    n08ControlMeanCoordinate S m (n08CircleColumn hS hR z u) = 0 := by
  have hd := (n08CircleColumn_hasLineDerivAt hS hN.2.2.1 hR hz hs u).clm_comp
    (n08ControlMeanCoordinate S m)
  have hz' : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε := by
    simpa only [n08_stateProjection_eq_self hS z.1 hs, Prod.eta] using hz
  exact hd.unique (n08CircleResidual_mean_zero_hasLineDerivAt hT hS hN hR z hz' m u hu)

/-- These entries are evaluated on the actual normalized physical basis. -/
def n08CircleDiagonal (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) (m : ℕ) : ℝ :=
  n08ControlMeanCoordinate S m (n08CircleColumn hS hR z (n08ControlBasis hS m))

theorem n08CircleColumn_mean_diagonal
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : CircleSpace S) (m : ℕ) :
    n08ControlRestriction S (n08CircleColumn hS hR z u) m =
      n08CircleDiagonal hS hR z m * n08ControlRestriction S u m := by
  let L : CircleSpace S →L[ℝ] ℝ := n08ControlMeanCoordinate S m
  let A : CircleSpace S →L[ℝ] ℝ := L.comp (n08CircleColumn hS hR z)
  have hb : L (n08ControlBasis hS m) = 1 := by
    rw [n08ControlMeanCoordinate_apply,
      n08ControlBasis_restriction hS m (n08_materialSample_H_pos hT hN.1.1 m), lp.single_apply_self]
  have hu : L (u - L u • n08ControlBasis hS m) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, hb, mul_one, sub_self]
  have hzder : A (u - L u • n08ControlBasis hS m) = 0 :=
    n08CircleColumn_mean_zero hT hS hN hR hz hs m _ hu
  rw [map_sub, map_smul, smul_eq_mul] at hzder
  have heq : A u = A (n08ControlBasis hS m) * L u := by linarith only [hzder]
  exact heq

/-- Once the numerical bound is established on the chosen neighborhood,
the bounded diagonal is the mean row of this very same circle derivative. -/
theorem n08CircleColumn_restriction_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hbound : ∀ m, |n08CircleDiagonal hS hR z m| ≤ 2) (u : CircleSpace S) :
    n08ControlRestriction S (n08CircleColumn hS hR z u) =
      n08ControlDiagonal (n08CircleDiagonal hS hR z) hbound (n08ControlRestriction S u) := by
  apply lp.ext
  funext m
  rw [n08ControlDiagonal_apply]
  exact n08CircleColumn_mean_diagonal hT hS hN hR hz hs u m

end ContinuousFlexibility.Statements
