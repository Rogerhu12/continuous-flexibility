import ContinuousFlexibility.Analysis.N08CircleDerivative
import ContinuousFlexibility.Analysis.N08RadialFlow

/-!
# The actual height row and its parameter factor

At zero parameter, the controlled radial profile and the left chart are
unchanged by a height variation. The actual return residual is therefore
constant on that line near the base state. Its genuine height derivative
vanishes, so the N02 derivative factors by `q` on the whole neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

def n08HeightDirection (S : PhysicalSpacesData) : HeightPair S →L[ℝ] AnnularState S :=
  (ContinuousLinearMap.id ℝ (HeightPair S)).prod
    ((0 : HeightPair S →L[ℝ] ℝ).prod
      ((0 : HeightPair S →L[ℝ] CircleSpace S).prod
        (0 : HeightPair S →L[ℝ] CircleSpace S)))

theorem n08HeightDirection_apply (S : PhysicalSpacesData) (η : HeightPair S) :
    n08HeightDirection S η = (η, (0, (0, 0))) := by
  simp only [n08HeightDirection, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply]

def n08CircleHeightDerivative (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) :
    HeightPair S →L[ℝ] CircleSpace S :=
  (n08CircleStateDerivative hS hR z).comp (n08HeightDirection S)

theorem n08CircleHeightDerivative_apply (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) (η : HeightPair S) :
    n08CircleHeightDerivative hS hR z η =
      n08CircleStateDerivative hS hR z (η, (0, (0, 0))) := by
  rw [n08CircleHeightDerivative, ContinuousLinearMap.comp_apply, n08HeightDirection_apply]

/-- Constancy follows from the actual ordinary flow and its inverses,
and persists for the projected representative on ambient height lines. -/
theorem n08CircleResidual_height_zero_hasLineDerivAt
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    (x : AnnularState S)
    (hx : (n08_stateProjection hS x, 0) ∈ stateNeighborhood S C base ε)
    (η : HeightPair S) :
    HasProjectiveLineDerivAt (fun y => (n08CircleResidual hS hR (y, 0)).val)
      0 x (η, (0, (0, 0))) := by
  have hc : Continuous (fun t : ℝ =>
      (n08_stateProjection hS (x + t • (η, (0, (0, 0)))), (0 : ℝ))) :=
    ((n08_stateProjection hS).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).prodMk continuous_const
  have ht : Tendsto (fun t : ℝ =>
      (n08_stateProjection hS (x + t • (η, (0, (0, 0)))), (0 : ℝ)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (n08_stateProjection hS x, (0 : ℝ))) := by
    simpa only [zero_smul, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev := ht.eventually ((n08_isOpen_stateNeighborhood S C base ε).mem_nhds hx)
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
  simp only [zero_add, zero_smul, add_zero]
  apply (tendsto_const_nhds (x := (0 : CircleSpace S)) :
    Tendsto (fun _ : ℝ => (0 : CircleSpace S)) (𝓝[≠] (0 : ℝ)) (𝓝 0)).congr'
  filter_upwards [hev] with t ht
  have htail : (n08_stateProjection hS (x + t • (η, (0, (0, 0))))).2 =
      (n08_stateProjection hS x).2 := by
    rw [map_add, map_smul, n08_stateProjection_heightDirection]
    simp only [Prod.snd_add, Prod.snd_smul, smul_zero, add_zero]
  rw [n08CircleResidual_projected_coe hS hR ht,
    n08CircleResidual_projected_coe hS hR hx,
    n08_returnResidual_zero_parameter_eq_of_tail hS hT hN hR ht hx
      (n08_stateProjection_mem hS _) (n08_stateProjection_mem hS x) htail,
    sub_self, smul_zero]

theorem n08CircleHeightDerivative_zero_parameter
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    (x : AnnularState S)
    (hx : (n08_stateProjection hS x, 0) ∈ stateNeighborhood S C base ε)
    (η : HeightPair S) : n08CircleHeightDerivative hS hR (x, 0) η = 0 := by
  rw [n08CircleHeightDerivative_apply]
  exact (n08CircleStateDerivative_hasLineDerivAt hS hN.2.2.1 hR hx (η, (0, (0, 0)))).unique
    (n08CircleResidual_height_zero_hasLineDerivAt hS hT hN hR x hx η)

/-- The height row is a continuous linear map at each parameter. Its
required `q` multiple is the genuine height derivative, also at zero. -/
def n08HeightRow (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) :
    HeightPair S →L[ℝ] CircleSpace S :=
  z.2⁻¹ • n08CircleHeightDerivative hS hR z

theorem n08HeightRow_apply (hS : IsPhysicalSpaces D T S)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ) (η : HeightPair S) :
    n08HeightRow hS hR z η = z.2⁻¹ • n08CircleHeightDerivative hS hR z η := by
  simp only [n08HeightRow, smul_apply]

theorem n08HeightRow_scaled
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ}
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε)
    (η : HeightPair S) :
    z.2 • n08HeightRow hS hR z η = n08CircleHeightDerivative hS hR z η := by
  rcases z with ⟨x, q⟩
  change q • n08HeightRow hS hR (x, q) η = n08CircleHeightDerivative hS hR (x, q) η
  by_cases hq : q = 0
  · subst q
    rw [zero_smul]
    exact (n08CircleHeightDerivative_zero_parameter hS hT hN hR x hz η).symm
  · rw [n08HeightRow_apply, smul_smul, mul_inv_cancel₀ hq, one_smul]

theorem n08HeightRow_hasLineDerivAt
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (η : HeightPair S) :
    HasProjectiveLineDerivAt (fun x => (n08CircleResidual hS hR (x, z.2)).val)
      (z.2 • n08HeightRow hS hR z η) z.1 (η, (0, (0, 0))) := by
  have hp : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε := by
    simpa only [n08_stateProjection_eq_self hS z.1 hs, Prod.eta] using hz
  rw [n08HeightRow_scaled hS hT hN hR hp η, n08CircleHeightDerivative_apply]
  exact n08CircleStateDerivative_hasLineDerivAt hS hN.2.2.1 hR hp (η, (0, (0, 0)))

end ContinuousFlexibility.Statements
