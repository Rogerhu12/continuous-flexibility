import ContinuousFlexibility.Analysis.N08CircleDerivative
import ContinuousFlexibility.Analysis.N08StateLinearOperations
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

set_option backward.isDefEq.respectTransparency false

private theorem heightProjectedLine_eventually_mem
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (P : E →L[ℝ] E) {U : Set (E × ℝ)} (hU : IsOpen U)
    {x : E} {q : ℝ} (hx : (P x, q) ∈ U) (v : E) :
    ∀ᶠ t : ℝ in 𝓝 0, (P (x + n08RealSMul t v), q) ∈ U := by
  have hc : Continuous (fun t : ℝ => (P (x + n08RealSMul t v), q)) :=
    (P.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).prodMk continuous_const
  have ht : Tendsto (fun t : ℝ => (P (x + n08RealSMul t v), q))
      (𝓝 0) (𝓝 (P x, q)) := by
    simpa only [n08RealSMul, zero_smul, add_zero] using hc.tendsto 0
  exact ht.eventually (hU.mem_nhds hx)

private theorem heightProjectedLine_tail
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (P : (E × F) →L[ℝ] (E × F)) (x : E × F) (η : E)
    (hη : P (η, (0 : F)) = (η, (0 : F))) (t : ℝ) :
    (P (x + n08RealSMul t (η, (0 : F)))).2 = (P x).2 := by
  simp only [n08RealSMul, map_add, map_smul, hη,
    Prod.snd_add, Prod.smul_snd, smul_zero, add_zero]

private theorem heightLine_zero_derivative
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (f : E → F) (x v : E)
    (h : ∀ᶠ t : ℝ in 𝓝 0, f (x + n08RealSMul t v) = f x) :
    HasProjectiveLineDerivAt f 0 x v := by
  simp only [n08RealSMul] at h
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
  simp only [zero_add, zero_smul, add_zero]
  apply (tendsto_const_nhds (x := (0 : F)) :
    Tendsto (fun _ : ℝ => (0 : F)) (𝓝[≠] (0 : ℝ)) (𝓝 0)).congr'
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with t ht
  rw [ht, sub_self, smul_zero]

private theorem heightLine_derivative_value
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {f : E → F} {df dg : F} {x v : E} (h : dg = df)
    (hd : HasProjectiveLineDerivAt f df x v) : HasProjectiveLineDerivAt f dg x v := by
  rw [h]
  exact hd

private theorem heightRow_scale_inverse
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    (q : ℝ) (v : F) (h : q = 0 → v = 0) : q • (q⁻¹ • v) = v := by
  by_cases hq : q = 0
  · simp only [hq, zero_smul, h hq]
  · rw [smul_smul, mul_inv_cancel₀ hq, one_smul]

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
      n08CircleStateDerivative hS hR z (η, (0, (0, 0))) :=
  (ContinuousLinearMap.comp_apply (n08CircleStateDerivative hS hR z)
    (n08HeightDirection S) η).trans
      (congrArg (n08CircleStateDerivative hS hR z) (n08HeightDirection_apply S η))

private theorem n08CircleResidual_height_zero_eq
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    (x : AnnularState S)
    (hx : (n08_stateProjection hS x, 0) ∈ stateNeighborhood S C base ε)
    (η : HeightPair S) (t : ℝ)
    (ht : (n08_stateProjection hS (x + n08StateSMul S t (η, (0, (0, 0)))), 0) ∈
      stateNeighborhood S C base ε) :
    (n08CircleResidual hS hR (x + n08StateSMul S t (η, (0, (0, 0))), 0)).val =
      (n08CircleResidual hS hR (x, 0)).val := by
  have htail : (n08_stateProjection hS (x + n08StateSMul S t (η, (0, (0, 0))))).2 =
      (n08_stateProjection hS x).2 := by
    simpa only [n08StateSMul, Prod.zero_eq_mk] using
      heightProjectedLine_tail (n08_stateProjection hS) x η
        (by simpa only [Prod.zero_eq_mk] using n08_stateProjection_heightDirection hS η) t
  exact (n08CircleResidual_projected_coe hS hR ht).trans
    ((n08_returnResidual_zero_parameter_eq_of_tail hS hT hN hR ht hx
      (n08_stateProjection_mem hS _) (n08_stateProjection_mem hS x) htail).trans
        (n08CircleResidual_projected_coe hS hR hx).symm)

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
  apply heightLine_zero_derivative
  have hev := heightProjectedLine_eventually_mem (n08_stateProjection hS)
    (n08_isOpen_stateNeighborhood S C base ε) hx (η, (0, (0, 0)))
  exact hev.mono (fun t ht => n08CircleResidual_height_zero_eq hS hT hN hR x hx η t ht)

theorem n08CircleHeightDerivative_zero_parameter
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    (x : AnnularState S)
    (hx : (n08_stateProjection hS x, 0) ∈ stateNeighborhood S C base ε)
    (η : HeightPair S) : n08CircleHeightDerivative hS hR (x, 0) η = 0 :=
  (n08CircleHeightDerivative_apply hS hR (x, 0) η).trans
    ((n08CircleStateDerivative_hasLineDerivAt hS hN.2.2.1 hR hx (η, (0, (0, 0)))).unique
      (n08CircleResidual_height_zero_hasLineDerivAt hS hT hN hR x hx η))

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
  apply (congrArg (fun u : CircleSpace S => n08RealSMul q u)
    (n08HeightRow_apply hS hR (x, q) η)).trans
  apply heightRow_scale_inverse
  intro hq
  subst q
  exact n08CircleHeightDerivative_zero_parameter hS hT hN hR x hz η

theorem n08HeightRow_hasLineDerivAt
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hR : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (η : HeightPair S) :
    HasProjectiveLineDerivAt (fun x => (n08CircleResidual hS hR (x, z.2)).val)
      (z.2 • n08HeightRow hS hR z η) z.1 (η, (0, (0, 0))) := by
  have hp : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε := by
    simpa only [n08_stateProjection_eq_self hS z.1 hs, Prod.eta] using hz
  exact heightLine_derivative_value
    ((n08HeightRow_scaled hS hT hN hR hp η).trans
      (n08CircleHeightDerivative_apply hS hR z η))
    (n08CircleStateDerivative_hasLineDerivAt hS hN.2.2.1 hR hp (η, (0, (0, 0))))

end ContinuousFlexibility.Statements
