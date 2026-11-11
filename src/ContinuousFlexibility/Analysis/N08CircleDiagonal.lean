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

set_option backward.isDefEq.respectTransparency false

private theorem n08_projected_affine_eventually
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (P : E →L[ℝ] F) (x v : E) (q : ℝ) {U : Set (F × ℝ)}
    (hU : IsOpen U) (hx : (P x, q) ∈ U) :
    ∀ᶠ t : ℝ in 𝓝 0, (P (x + n08RealSMul t v), q) ∈ U := by
  have hc : Continuous (fun t : ℝ => (P (x + n08RealSMul t v), q)) :=
    (P.continuous.comp (continuous_const.add
      (continuous_id.smul continuous_const))).prodMk continuous_const
  have ht : Tendsto (fun t : ℝ => (P (x + n08RealSMul t v), q))
      (𝓝 0) (𝓝 (P x, q)) := by
    simpa only [n08RealSMul, zero_smul, add_zero] using hc.tendsto 0
  exact ht.eventually (hU.mem_nhds hx)

theorem n08_affine_parameter_eventually
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (x v : E) (q : ℝ) {U : Set (E × ℝ)} (hU : IsOpen U) (hx : (x, q) ∈ U) :
    ∀ᶠ t : ℝ in 𝓝 0, (x + n08RealSMul t v, q) ∈ U :=
  n08_projected_affine_eventually (ContinuousLinearMap.id ℝ E) x v q hU hx

private theorem n08_line_zero_derivative
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ) (x v : E)
    (h : (fun t : ℝ => f (x + n08RealSMul t v)) =ᶠ[𝓝 0] fun _ => f x) :
    HasProjectiveLineDerivAt f 0 x v := by
  unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
  simp only [zero_add, zero_smul, add_zero]
  apply (tendsto_const_nhds (x := (0 : ℝ)) :
    Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] (0 : ℝ)) (𝓝 0)).congr'
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with t ht
  change f (x + t • v) = f x at ht
  rw [ht, sub_self, smul_zero]

private theorem n08_kappaLine_coordinates
    {H K : Type*} [AddCommGroup H] [Module ℝ H]
    [AddCommGroup K] [Module ℝ K]
    (x : H × (ℝ × (K × K))) (u : K) (t : ℝ) :
    (x + n08RealSMul t (0, (0, (u, 0)))).1 = x.1 ∧
    (x + n08RealSMul t (0, (0, (u, 0)))).2.1 = x.2.1 ∧
    (x + n08RealSMul t (0, (0, (u, 0)))).2.2.2 = x.2.2.2 := by
  simp only [n08RealSMul, Prod.smul_mk, Prod.fst_add, Prod.snd_add,
    smul_zero, add_zero, and_self]

private theorem n08_projected_linear_observation_fixed
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (f : E → ℝ) (L : E →L[ℝ] ℝ) (hf : ∀ x, L x = f x)
    (P : E → E) (hP : ∀ x, f (P x) = f x)
    (x v : E) (hv : f v = 0) (t : ℝ) :
    f (P (x + n08RealSMul t v)) = f (P x) := by
  rw [hP, hP, ← hf, ← hf]
  change L (x + t • v) = L x
  rw [map_add, map_smul, hf v, hv, smul_zero, add_zero]

private theorem n08_scalar_row_diagonal
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (L : E →L[ℝ] ℝ) (A : E →L[ℝ] E) (e : E)
    (he : L e = 1) (hker : ∀ u, L u = 0 → L (A u) = 0) (u : E) :
    L (A u) = L (A e) * L u := by
  have hz : L (u - L u • e) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, he, mul_one, sub_self]
  have hd := hker (u - L u • e) hz
  rw [map_sub, map_smul, map_sub, map_smul, smul_eq_mul] at hd
  linarith only [hd]

private theorem n08_controlDiagonal_eq_of_coordinates
    (a : ℕ → ℝ) (ha : ∀ m, |a m| ≤ 2) (f g : ControlBanach)
    (h : ∀ m, f m = a m * g m) : f = n08ControlDiagonal a ha g := by
  apply lp.ext
  funext m
  exact (h m).trans (n08ControlDiagonal_apply a ha g m).symm

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

private theorem n08ControlMeanCoordinate_eq_of_decode
    (hS : IsPhysicalSpaces D T S) (m : ℕ) (u v : CircleSpace S)
    (h : (S.circle (3 / 4 : ℝ)).decode u m =
      (S.circle (3 / 4 : ℝ)).decode v m) :
    n08ControlMeanCoordinate S m u = n08ControlMeanCoordinate S m v :=
  (n08ControlMeanCoordinate_apply S m u).trans
    ((n08ControlRestriction_apply hS u m).trans
      ((congrArg (fun f : ℝ → ℝ =>
        T.H (T.sample m) ^ (-(3 / 4 : ℝ)) * angularMean f) h).trans
        ((n08ControlRestriction_apply hS v m).symm.trans
          (n08ControlMeanCoordinate_apply S m v).symm)))

private theorem n08CircleResidual_mean_eq_of_projected_decode
    (hS : IsPhysicalSpaces D T S) (hR : N02Properties D T S C R base ε)
    (z w : AnnularState S × ℝ)
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε)
    (hw : (n08_stateProjection hS w.1, w.2) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (h : (S.circle (3 / 4 : ℝ)).decode
        (R.residual (n08_stateProjection hS z.1, z.2)) m =
      (S.circle (3 / 4 : ℝ)).decode
        (R.residual (n08_stateProjection hS w.1, w.2)) m) :
    n08ControlMeanCoordinate S m (n08CircleResidual hS hR z).val =
      n08ControlMeanCoordinate S m (n08CircleResidual hS hR w).val :=
  (congrArg (n08ControlMeanCoordinate S m)
      (n08CircleResidual_projected_coe hS hR hz)).trans
    ((n08ControlMeanCoordinate_eq_of_decode hS m _ _ h).trans
      (congrArg (n08ControlMeanCoordinate S m)
        (n08CircleResidual_projected_coe hS hR hw)).symm)

theorem n08_materialSample_H_pos (hT : IsMaterialData D T)
    (hRef : IsAccumulatingProfile D) (m : ℕ) : 0 < T.H (T.sample m) :=
  (hT.2.1 _ (materialSample_mem_radialCore hT hRef.choose_spec.2.1 m)).2.1

theorem n08_kappaLine_fixed_coordinates (S : PhysicalSpacesData)
    (x : AnnularState S) (u : CircleSpace S) (t : ℝ) :
    (x + n08StateSMul S t (0, (0, (u, 0)))).1 = x.1 ∧
    (x + n08StateSMul S t (0, (0, (u, 0)))).2.1 = x.2.1 ∧
    (x + n08StateSMul S t (0, (0, (u, 0)))).2.2.2 = x.2.2.2 :=
  n08_kappaLine_coordinates x u t

private theorem n08_projected_kappa_line_fixed (hS : IsPhysicalSpaces D T S)
    (x v : AnnularState S) (m : ℕ) (hv : stateKappa S v m = 0) (t : ℝ) :
    stateKappa S (n08_stateProjection hS (x + n08StateSMul S t v)) m =
      stateKappa S (n08_stateProjection hS x) m :=
  n08_projected_linear_observation_fixed (fun y => stateKappa S y m)
    (n08_stateKappaEvalCLM hS m) (n08_stateKappaEvalCLM_apply hS m)
    (n08_stateProjection hS) (fun y => n08_stateKappa_projection hS y m) x v hv t

private theorem n08_projected_chart_eq (hS : IsPhysicalSpaces D T S)
    (x y : AnnularState S) (m : ℕ) (h : x.2.2.2 = y.2.2.2) :
    stateLeftChart S (n08_stateProjection hS x) m =
      stateLeftChart S (n08_stateProjection hS y) m := by
  funext θ
  exact congrArg (fun a : ℝ => θ + a)
    ((n08_stateProjection_chart_decode hS x m θ).trans
      ((congrArg (fun u : CircleSpace S =>
        ((S.circle (3 / 4 : ℝ)).decode u m θ -
          (S.circle (3 / 4 : ℝ)).decode u m (-θ)) / 2) h).trans
        (n08_stateProjection_chart_decode hS y m θ).symm))

private theorem n08CircleResidual_mean_zero_line_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ)
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (u : CircleSpace S) (hu : n08ControlMeanCoordinate S m u = 0)
    (t : ℝ) (ht : (n08_stateProjection hS
      (z.1 + n08StateSMul S t (0, (0, (u, 0)))), z.2) ∈ stateNeighborhood S C base ε) :
    n08ControlMeanCoordinate S m
        (n08CircleResidual hS hR (z.1 + n08StateSMul S t (0, (0, (u, 0))), z.2)).val =
      n08ControlMeanCoordinate S m (n08CircleResidual hS hR z).val := by
  let v : AnnularState S := (0, (0, (u, 0)))
  have hmean : stateKappa S v m = 0 := by
    rw [n08ControlMeanCoordinate_apply, n08ControlRestriction_apply hS] at hu
    exact (mul_eq_zero.mp hu).resolve_left
      (Real.rpow_pos_of_pos (n08_materialSample_H_pos hT hN.1.1 m) _).ne'
  have hcoord := n08_kappaLine_fixed_coordinates S z.1 u t
  have hheight : (n08_stateProjection hS (z.1 + n08StateSMul S t v)).1 =
      (n08_stateProjection hS z.1).1 := by
    exact (n08_stateProjection_height hS _).trans
      (hcoord.1.trans (n08_stateProjection_height hS z.1).symm)
  have hν : (n08_stateProjection hS (z.1 + n08StateSMul S t v)).2.1 =
      (n08_stateProjection hS z.1).2.1 := by
    exact (n08_stateProjection_nu hS _).trans
      (hcoord.2.1.trans (n08_stateProjection_nu hS z.1).symm)
  have hκ : stateKappa S (n08_stateProjection hS (z.1 + n08StateSMul S t v)) m =
      stateKappa S (n08_stateProjection hS z.1) m :=
    n08_projected_kappa_line_fixed hS z.1 v m hmean t
  have hchart : stateLeftChart S (n08_stateProjection hS (z.1 + n08StateSMul S t v)) m =
      stateLeftChart S (n08_stateProjection hS z.1) m :=
    n08_projected_chart_eq hS _ _ m hcoord.2.2
  exact n08CircleResidual_mean_eq_of_projected_decode hS hR _ z ht hz m
    (funext fun θ => n08_returnResidual_component_eq hT hS hN hR ht hz
      (n08_stateProjection_mem hS _) (n08_stateProjection_mem hS _) hheight hν hκ hchart θ)

private theorem n08CircleResidual_mean_zero_hasLineDerivAt
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) (z : AnnularState S × ℝ)
    (hz : (n08_stateProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε)
    (m : ℕ) (u : CircleSpace S) (hu : n08ControlMeanCoordinate S m u = 0) :
    HasProjectiveLineDerivAt
      (fun x => n08ControlMeanCoordinate S m (n08CircleResidual hS hR (x, z.2)).val)
      0 z.1 (0, (0, (u, 0))) :=
  n08_line_zero_derivative _ z.1 (0, (0, (u, 0)))
    ((n08_projected_affine_eventually (n08_stateProjection hS) z.1 (0, (0, (u, 0))) z.2
      (n08_isOpen_stateNeighborhood S C base ε) hz).mono
      (fun t ht => n08CircleResidual_mean_zero_line_eq hT hS hN hR z hz m u hu t ht))

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
  have hb : L (n08ControlBasis hS m) = 1 := by
    rw [n08ControlMeanCoordinate_apply,
      n08ControlBasis_restriction hS m (n08_materialSample_H_pos hT hN.1.1 m), lp.single_apply_self]
  have heq := n08_scalar_row_diagonal L (n08CircleColumn hS hR z) (n08ControlBasis hS m) hb
    (fun v hv => n08CircleColumn_mean_zero hT hS hN hR hz hs m v hv) u
  change n08ControlRestriction S (n08CircleColumn hS hR z u) m =
    n08ControlMeanCoordinate S m (n08CircleColumn hS hR z (n08ControlBasis hS m)) *
      n08ControlRestriction S u m
  simpa only [L, n08ControlMeanCoordinate_apply] using heq

/-- Once the numerical bound is established on the chosen neighborhood,
the bounded diagonal is the mean row of this very same circle derivative. -/
theorem n08CircleColumn_restriction_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hbound : ∀ m, |n08CircleDiagonal hS hR z m| ≤ 2) (u : CircleSpace S) :
    n08ControlRestriction S (n08CircleColumn hS hR z u) =
      n08ControlDiagonal (n08CircleDiagonal hS hR z) hbound (n08ControlRestriction S u) :=
  n08_controlDiagonal_eq_of_coordinates (n08CircleDiagonal hS hR z) hbound _ _
    (fun m => n08CircleColumn_mean_diagonal hT hS hN hR hz hs u m)

end ContinuousFlexibility.Statements
