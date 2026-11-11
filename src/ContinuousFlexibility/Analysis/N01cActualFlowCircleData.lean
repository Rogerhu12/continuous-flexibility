import ContinuousFlexibility.Analysis.N01cActualFlowSmoothDirections
import ContinuousFlexibility.Analysis.N01cFlowVariationCircleData
import ContinuousFlexibility.Analysis.N01cStateAngleIdentification

/-!
# Circle variation data of the supplied ordinary flow

The finite parameter compression stays in the original state neighbourhood
and is the identity near the selected state. The smooth compact time map
acts on the same supplied trajectories. Consequently its global smooth
finite-parameter variations are the actual state jets of `minusFlow`.

The circle linear equation and Sobolev estimate therefore apply to those
actual jets. Neither a flow parameter derivative nor a flow norm estimate
is an input. The speed tower is the internal actual-speed input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

section CompressionChoice

variable {E P : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

private theorem exists_flowPlotCompression {U : Set E}
    (hU : IsOpen U) (x : E) (hx : x ∈ U) (L : P →L[ℝ] E) :
    ∃ ρ : P → P, ContDiff ℝ ∞ ρ ∧ ρ 0 = 0 ∧
      (∀ q, x + L (ρ q) ∈ U) ∧ ρ =ᶠ[𝓝 (0 : P)] id := by
  have hV : IsOpen ((fun q => x + L q) ⁻¹' U) :=
    hU.preimage (continuous_const.add L.continuous)
  have h0 : (0 : P) ∈ (fun q => x + L q) ⁻¹' U := by
    simpa only [mem_preimage, map_zero, add_zero] using hx
  exact exists_smooth_neighbourhood_compression hV h0

/-- One compression is selected before any order of differentiation. -/
def flowPlotCompression {U : Set E}
    (hU : IsOpen U) (x : E) (hx : x ∈ U) (L : P →L[ℝ] E) : P → P :=
  Classical.choose (exists_flowPlotCompression hU x hx L)

theorem flowPlotCompression_spec {U : Set E}
    (hU : IsOpen U) (x : E) (hx : x ∈ U) (L : P →L[ℝ] E) :
    ContDiff ℝ ∞ (flowPlotCompression hU x hx L) ∧
      flowPlotCompression hU x hx L 0 = 0 ∧
      (∀ q, x + L (flowPlotCompression hU x hx L q) ∈ U) ∧
      flowPlotCompression hU x hx L =ᶠ[𝓝 (0 : P)] id :=
  Classical.choose_spec (exists_flowPlotCompression hU x hx L)

end CompressionChoice

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency true

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

section PlotDefinitions

variable {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {base : ℕ} {ε : ℝ} {d : ℕ}
  (x : AnnularState S × ℝ) (hx : x ∈ stateNeighborhood S C base ε)
  (L : (Fin d → ℝ) →L[ℝ] (AnnularState S × ℝ))

/-- The actual state in one compressed finite affine plot. -/
def ordinaryFlowFiniteState (q : Fin d → ℝ) : AnnularState S × ℝ :=
  x + L (flowPlotCompression (isOpen_stateNeighborhood S C base ε) x hx L q)

theorem ordinaryFlowFiniteState_mem (q : Fin d → ℝ) :
    ordinaryFlowFiniteState x hx L q ∈ stateNeighborhood S C base ε :=
  (flowPlotCompression_spec (isOpen_stateNeighborhood S C base ε) x hx L).2.2.1 q

@[simp] theorem ordinaryFlowFiniteState_zero :
    ordinaryFlowFiniteState x hx L 0 = x := by
  simp only [ordinaryFlowFiniteState,
    (flowPlotCompression_spec (isOpen_stateNeighborhood S C base ε) x hx L).2.1,
    map_zero, add_zero]

theorem continuous_ordinaryFlowFiniteState :
    Continuous (ordinaryFlowFiniteState x hx L) :=
  continuous_const.add (L.continuous.comp
    (flowPlotCompression_spec (isOpen_stateNeighborhood S C base ε) x hx L).1.continuous)

theorem ordinaryFlowFiniteState_eventuallyEq :
    ordinaryFlowFiniteState x hx L =ᶠ[𝓝 (0 : Fin d → ℝ)] (fun q => x + L q) := by
  filter_upwards
    [(flowPlotCompression_spec (isOpen_stateNeighborhood S C base ε) x hx L).2.2.2]
      with q hq
  simp only [ordinaryFlowFiniteState, hq, id_eq]

/-- The real-time smooth speed along the same finite parameter plot. -/
def ordinaryFlowFiniteSpeed (D : ReferenceData) (m : ℕ)
    (p : (Fin d → ℝ) × PolarPoint) : ℝ :=
  deriv (circleFlowCompactTime 0 Real.pi) p.2.1 *
    componentCosineSpeed D S C m
      (ordinaryFlowFiniteState x hx L p.1,
        (circleFlowCompactTime 0 Real.pi p.2.1, p.2.2))

/-- The original ordinary trajectory under the same state and time maps. -/
def ordinaryFlowFiniteTrajectory (m : ℕ)
    (p : (Fin d → ℝ) × PolarPoint) : ℝ :=
  ordinaryFlowInCosineTime C m
    (ordinaryFlowFiniteState x hx L p.1,
      (circleFlowCompactTime 0 Real.pi p.2.1, p.2.2))

theorem ordinaryFlowFiniteTrajectory_zero (m : ℕ) (p : PolarPoint) :
    ordinaryFlowFiniteTrajectory x hx L m (0, p) =
      ordinaryFlowInCosineTime C m
        (x, (circleFlowCompactTime 0 Real.pi p.1, p.2)) := by
  simp only [ordinaryFlowFiniteTrajectory, ordinaryFlowFiniteState_zero]

end PlotDefinitions

section ActualPlots

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
  (hpos : ∀ z ∈ stateNeighborhood S C base ε, ∀ i r,
    r ∈ Icc (C.left i) (C.right i) →
      0 < twoRootDivided (componentOpticalSquare D S C i z) (C.left i) (C.right i) r)
  (m : ℕ)
  (J : ContinuousTimeSpeedTower (stateNeighborhood S C base ε)
    (componentCosineSpeed D S C m))
  {d : ℕ} (x : AnnularState S × ℝ) (hx : x ∈ stateNeighborhood S C base ε)
  (L : (Fin d → ℝ) →L[ℝ] (AnnularState S × ℝ))

include hS hT hA hB hpos

theorem contDiff_ordinaryFlowFiniteSpeed :
    ContDiff ℝ ∞ (ordinaryFlowFiniteSpeed x hx L D m) := by
  have hρ := (flowPlotCompression_spec
    (isOpen_stateNeighborhood S C base ε) x hx L).1
  have hd : ContDiff ℝ ∞ (deriv (circleFlowCompactTime 0 Real.pi)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_circleFlowCompactTime 0 Real.pi)).2
  have hc := (contDiffOn_componentCosineSpeed_finiteAffine hS hT hA hB hpos m x L).comp_contDiff
      ((hρ.comp contDiff_fst).prodMk
        (((contDiff_circleFlowCompactTime 0 Real.pi).comp contDiff_snd.fst).prodMk contDiff_snd.snd))
      (fun p => ⟨ordinaryFlowFiniteState_mem x hx L p.1, mem_univ _⟩)
  exact (hd.comp contDiff_snd.fst).mul hc

include J in
theorem continuous_ordinaryFlowFiniteTrajectory :
    Continuous (ordinaryFlowFiniteTrajectory x hx L m) :=
  (continuousOn_ordinaryFlowInCosineTime hS hT hA hB hpos m J).comp_continuous
    (((continuous_ordinaryFlowFiniteState x hx L).comp continuous_fst).prodMk
      (((contDiff_circleFlowCompactTime 0 Real.pi).continuous.comp continuous_snd.fst).prodMk continuous_snd.snd))
    (fun p => ⟨ordinaryFlowFiniteState_mem x hx L p.1,
      circleFlowCompactTime_mem Real.pi_pos.le p.2.1, mem_univ _⟩)

theorem ordinaryFlowFiniteTrajectory_initial (q : Fin d → ℝ) (θ : ℝ) :
    ordinaryFlowFiniteTrajectory x hx L m (q, (0, θ)) = θ := by
  change C.minusFlow (ordinaryFlowFiniteState x hx L q) m
    (rootCosinePath (C.left m) (C.right m)
      (circleFlowCompactTime 0 Real.pi 0)) θ = θ
  rw [circleFlowCompactTime_zero]
  exact componentCosineFlow_initial hB (ordinaryFlowFiniteState_mem x hx L q) m θ

theorem ordinaryFlowFiniteTrajectory_hasDerivAt (q : Fin d → ℝ) (t θ : ℝ) :
    HasDerivAt (fun r => ordinaryFlowFiniteTrajectory x hx L m (q, (r, θ)))
      (ordinaryFlowFiniteSpeed x hx L D m
        (q, (t, ordinaryFlowFiniteTrajectory x hx L m (q, (t, θ))))) t := by
  have hz := ordinaryFlowFiniteState_mem x hx L q
  exact hasDerivAt_timeChange_classicalTrajectory Real.pi_pos.le
    (contDiff_componentCosineSpeed hS hT hA hB hpos hz m).continuous
    (continuousOn_componentCosineFlow hA hB hz m θ)
    (fun r hr => hasDerivAt_componentCosineFlow hS hT hA hB hz m θ hr)
    (circleFlowCompactTime_mem Real.pi_pos.le)
    (((contDiff_circleFlowCompactTime 0 Real.pi).differentiable (by simp) t).hasDerivAt)

theorem ordinaryFlowFiniteSpeed_periodic (q : Fin d → ℝ) (t : ℝ) :
    Function.Periodic
      (fun θ => ordinaryFlowFiniteSpeed x hx L D m (q, (t, θ))) Real.pi := by
  intro θ
  change deriv (circleFlowCompactTime 0 Real.pi) t *
      componentCosineSpeed D S C m
        (ordinaryFlowFiniteState x hx L q,
          (circleFlowCompactTime 0 Real.pi t, θ + Real.pi)) = _
  rw [componentCosineSpeed_periodic hS (ordinaryFlowFiniteState x hx L q) m
    (circleFlowCompactTime 0 Real.pi t) θ]

theorem ordinaryFlowFiniteTrajectory_periodic_lift
    (q : Fin d → ℝ) (t θ : ℝ) :
    ordinaryFlowFiniteTrajectory x hx L m (q, (t, θ + Real.pi)) =
      ordinaryFlowFiniteTrajectory x hx L m (q, (t, θ)) + Real.pi := by
  exact ((hB.1 _ (ordinaryFlowFiniteState_mem x hx L q) m θ).2.2.2
    (rootCosinePath (C.left m) (C.right m) (circleFlowCompactTime 0 Real.pi t))
    (rootCosinePath_mem_Icc (hA.2.2.1.1 m).2.1.le _)).2

include J in
theorem contDiff_ordinaryFlowFiniteTrajectory :
    ContDiff ℝ ∞ (ordinaryFlowFiniteTrajectory x hx L m) :=
  contDiff_globalCircleVectorFlow
    (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L)
    (continuous_ordinaryFlowFiniteTrajectory hS hT hA hB hpos m J x hx L)
    (ordinaryFlowFiniteTrajectory_initial hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_hasDerivAt hS hT hA hB hpos m x hx L)

/-- The speed jets in the global finite plot are exactly the original
joint speed jets at the chosen state, with the true time multiplier. -/
theorem ordinaryFlowFiniteSpeedTower_D_apply
    (n : ℕ) (t θ : ℝ) (v : Fin n → (Fin d → ℝ) × ℝ) :
    (continuousTimeSpeedTowerOfContDiff
      (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L)).D n (0, (t, θ)) v =
      deriv (circleFlowCompactTime 0 Real.pi) t *
        J.D n (x, (circleFlowCompactTime 0 Real.pi t, θ))
          (fun i => flowStateAngleMap L (v i)) := by
  let τ := circleFlowCompactTime 0 Real.pi
  let Q := J.timeChange (contDiff_circleFlowCompactTime 0 Real.pi)
  have he :
      (fun q : (Fin d → ℝ) × ℝ =>
        ordinaryFlowFiniteSpeed x hx L D m (q.1, (t, q.2))) =ᶠ[𝓝 (0, θ)]
      (fun q => timeChangedTopologicalSpeed (componentCosineSpeed D S C m) τ
        (x + L q.1, (t, q.2))) := by
    filter_upwards [continuousAt_fst.tendsto.eventually
      (ordinaryFlowFiniteState_eventuallyEq x hx L)] with q hq
    simp only [ordinaryFlowFiniteSpeed, timeChangedTopologicalSpeed, hq, τ]
  have hpoint : (x, (0 : ℝ)) + flowStateAngleMap L (0, θ) ∈
      stateNeighborhood S C base ε ×ˢ (univ : Set ℝ) := by
    simpa only [flowStateAngleMap_apply, map_zero, Prod.mk_add_mk, add_zero, zero_add] using
      (show (x, θ) ∈ stateNeighborhood S C base ε ×ˢ (univ : Set ℝ)
        from ⟨hx, mem_univ _⟩)
  have ha := smoothDirections_iteratedFDeriv_finiteAffine
    (Q.jet t) (x, (0 : ℝ)) (flowStateAngleMap L) n hpoint v
  have hejet := congrArg (fun A : ((Fin d → ℝ) × ℝ) [×n]→L[ℝ] ℝ => A v)
    ((he.iteratedFDeriv ℝ n).self_of_nhds)
  rw [continuousTimeSpeedTowerOfContDiff_D_apply]
  calc
    _ = iteratedFDeriv ℝ n
        (fun q : (Fin d → ℝ) × ℝ =>
          timeChangedTopologicalSpeed (componentCosineSpeed D S C m) τ
            (x + L q.1, (t, q.2))) (0, θ) v := hejet
    _ = Q.D n (x, (t, θ)) (fun i => flowStateAngleMap L (v i)) := by
      simpa only [flowStateAngleMap_apply, map_zero, Prod.mk_add_mk,
        add_zero, zero_add] using ha
    _ = _ := rfl

/-- Every angular derivative of a finite-plot parameter jet is the
evaluation of the same canonical actual angular state tower. -/
theorem ordinaryFlowFiniteTrajectory_parameterAngularJet
    (n b : ℕ) (t θ : ℝ) (v : Fin n → (Fin d → ℝ)) :
    iteratedDeriv b
      (fun η => flowParameterField (ordinaryFlowFiniteTrajectory x hx L m) n 0 v (t, η)) θ =
      (ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m J
        (rootCosinePath_mem_Icc (hA.2.2.1.1 m).2.1.le
          (circleFlowCompactTime 0 Real.pi t)) b θ).D n x (fun i => L (v i)) := by
  let r := rootCosinePath (C.left m) (C.right m) (circleFlowCompactTime 0 Real.pi t)
  have hr : r ∈ Icc (C.left m) (C.right m) :=
    rootCosinePath_mem_Icc (hA.2.2.1.1 m).2.1.le _
  let Ja := ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m J hr
  have he (η : ℝ) :
      flowParameterField (ordinaryFlowFiniteTrajectory x hx L m) n 0 v (t, η) =
        (Ja 0 η).D n x (fun i => L (v i)) := by
    have hevent :
        (fun q : Fin d → ℝ => ordinaryFlowFiniteTrajectory x hx L m (q, (t, η))) =ᶠ[𝓝 0]
        (fun q => C.minusFlow (x + L q) m r η) := by
      filter_upwards [ordinaryFlowFiniteState_eventuallyEq x hx L] with q hq
      simp only [ordinaryFlowFiniteTrajectory, ordinaryFlowInCosineTime, hq, r]
    have hpoint : x + L 0 ∈ stateNeighborhood S C base ε := by
      simpa only [map_zero, add_zero] using hx
    have ha := smoothDirections_iteratedFDeriv_finiteAffine (Ja 0 η) x L n hpoint v
    calc
      _ = iteratedFDeriv ℝ n (fun q => C.minusFlow (x + L q) m r η) 0 v :=
        congrArg (fun A : (Fin d → ℝ) [×n]→L[ℝ] ℝ => A v)
          ((hevent.iteratedFDeriv ℝ n).self_of_nhds)
      _ = _ := by simpa only [iteratedDeriv_zero, map_zero, add_zero] using ha
  rw [show (fun η => flowParameterField
    (ordinaryFlowFiniteTrajectory x hx L m) n 0 v (t, η)) =
      (fun η => (Ja 0 η).D n x (fun i => L (v i))) from funext he]
  exact iteratedDeriv_stateJet_angle (isOpen_stateNeighborhood S C base ε)
    (isFiniteAffineTimeSmooth_of_jointSmoothDirections
      (ordinaryFlowJointSmoothDirections hS hT hA hB hpos m J hr))
    (fun b q => Ja b q.2) b n hx (0 : ℝ) θ (fun i => L (v i))

/-- The positive finite parameter variation of the supplied ordinary
trajectory, as actual circle linear-ODE data on the compact time interval. -/
def ordinaryFlowCircleVariationData (n : ℕ) (v : Fin (n + 1) → (Fin d → ℝ)) :
    CircleLinearVariationData Real.pi 0 1 :=
  flowParameterCircleVariationData
    (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L)
    (continuousTimeSpeedTowerOfContDiff
      (contDiff_ordinaryFlowFiniteSpeed hS hT hA hB hpos m x hx L))
    (continuous_ordinaryFlowFiniteTrajectory hS hT hA hB hpos m J x hx L)
    (ordinaryFlowFiniteTrajectory_initial hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_hasDerivAt hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteSpeed_periodic hS hT hA hB hpos m x hx L)
    (ordinaryFlowFiniteTrajectory_periodic_lift hS hT hA hB hpos m x hx L)
    1 n 0 v

theorem ordinaryFlowCircleVariationData_value
    (n : ℕ) (v : Fin (n + 1) → (Fin d → ℝ)) (t : ℝ) (b : ℕ) (θ : ℝ) :
    (ordinaryFlowCircleVariationData hS hT hA hB hpos m J x hx L n v).value t b (θ : AddCircle Real.pi) =
      (ordinaryFlowAngularStateSmoothDirections hS hT hA hB hpos m J
        (rootCosinePath_mem_Icc (hA.2.2.1.1 m).2.1.le
          (circleFlowCompactTime 0 Real.pi t)) b θ).D (n + 1) x (fun i => L (v i)) := by
  rw [ordinaryFlowCircleVariationData, flowParameterCircleVariationData_value]
  exact ordinaryFlowFiniteTrajectory_parameterAngularJet
    hS hT hA hB hpos m J x hx L (n + 1) b t θ v

/-- This is the actual Sobolev estimate for the actual positive state
variation; its coefficient and source are the actual ones defined above. -/
theorem ordinaryFlowCircleVariationData_sobolev_le
    (n : ℕ) (v : Fin (n + 1) → (Fin d → ℝ)) (s : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let V := ordinaryFlowCircleVariationData hS hT hA hB hpos m J x hx L n v
    V.valueNorm s t ≤ circleLinearVariationSobolevConstant Real.pi (V.coefficientSize 1) s *
      (V.forcingSize s + V.coefficientSize s * V.forcingSize 1) :=
  (ordinaryFlowCircleVariationData hS hT hA hB hpos m J x hx L n v).sobolev_le s ht

end ActualPlots

end ContinuousFlexibility.Statements
