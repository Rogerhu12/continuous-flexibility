module

public import ContinuousFlexibility.Analysis.N04NegativeChartRootLabelPrefix
public import ContinuousFlexibility.Analysis.N04RealizationRootBoundaryDirections
public import ContinuousFlexibility.Analysis.N01cActualFlowCircleData

/-!
# A genuine global finite-plot representative of each root label

Only the state coordinates are compressed. The same open state
neighbourhood works for every angle and every derivative order. All
jets at the centre are the original sector jets on the affine images
of their slots; no quantitative estimate on the extension is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements CanonicalGeometry
open scoped Topology ContDiff

variable {E P : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- A single state compression leaves the complete angular fibre
unchanged near the centre of a finite affine plot. -/
theorem n04NegativeChart_finiteStateAngle_representative
    {U : Set E} {g : E × ℝ → ℝ} (hU : IsOpen U)
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) g)
    (x : E) (hx : x ∈ U) (L : P →L[ℝ] E) :
    ∃ h : P × ℝ → ℝ, ContDiff ℝ ∞ h ∧
      ∃ V : Set P, IsOpen V ∧ (0 : P) ∈ V ∧
        (∀ y ∈ V, x + L y ∈ U) ∧
        ∀ y ∈ V, ∀ θ, h (y, θ) = g (x + L y, θ) := by
  let ρ := flowPlotCompression hU x hx L
  have hρ := flowPlotCompression_spec hU x hx L
  let Ψ : P × ℝ → P × ℝ := fun q => (ρ q.1, q.2)
  have hΨ : ContDiff ℝ ∞ Ψ := (hρ.1.comp contDiff_fst).prodMk contDiff_snd
  have hmap (q : P × ℝ) :
      (x, (0 : ℝ)) + flowStateAngleMap L (Ψ q) ∈ U ×ˢ (univ : Set ℝ) := by
    change x + L (ρ q.1) ∈ U ∧ (0 : ℝ) + q.2 ∈ (univ : Set ℝ)
    exact ⟨hρ.2.2.1 q.1, mem_univ _⟩
  have hs := (smoothDirections_contDiffOn_finiteAffine
    J (x, (0 : ℝ)) (flowStateAngleMap L)).comp_contDiff hΨ hmap
  let h : P × ℝ → ℝ := fun q => g (x + L (ρ q.1), q.2)
  have hh : ContDiff ℝ ∞ h := by
    simpa only [h, Ψ, Function.comp_def, flowStateAngleMap_apply,
      Prod.mk_add_mk, zero_add] using hs
  obtain ⟨V, hVeq, hV, h0⟩ := mem_nhds_iff.mp hρ.2.2.2
  refine ⟨h, hh, V, hV, h0, ?_, ?_⟩
  · intro y hy
    have he : flowPlotCompression hU x hx L y = y := hVeq hy
    simpa only [he] using hρ.2.2.1 y
  · intro y hy θ
    exact congrArg (fun u : P => g (x + L u, θ)) (hVeq hy)

/-- The scalar angular tower of a representative is exactly the
original tower on arbitrary affine images of parameter slots. -/
theorem n04NegativeChart_finiteRepresentative_angularJet
    {U : Set E} {g : E × ℝ → ℝ} {h : P × ℝ → ℝ}
    {V : Set P} (hV : IsOpen V) (h0 : (0 : P) ∈ V)
    (x : E) (hx : x ∈ U) (L : P →L[ℝ] E)
    (heq : ∀ y ∈ V, ∀ θ, h (y, θ) = g (x + L y, θ))
    (b : ℕ) (θ : ℝ)
    (Ja : SmoothDirections U (fun z => iteratedDeriv b (fun η => g (z, η)) θ))
    (k : ℕ) (v : Fin k → P) :
    iteratedFDeriv ℝ k (fun y => iteratedDeriv b (fun η => h (y, η)) θ) 0 v =
      Ja.D k x (fun i => L (v i)) := by
  have hevent : (fun y => iteratedDeriv b (fun η => h (y, η)) θ) =ᶠ[𝓝 (0 : P)]
      (fun y => iteratedDeriv b (fun η => g (x + L y, η)) θ) := by
    filter_upwards [hV.mem_nhds h0] with y hy
    exact congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ) (funext (heq y hy))
  have hpoint : x + L (0 : P) ∈ U := by
    simpa only [map_zero, add_zero] using hx
  have ha := smoothDirections_iteratedFDeriv_finiteAffine Ja x L k (y := 0) hpoint v
  exact (congrArg (fun A : P [×k]→L[ℝ] ℝ => A v)
    ((hevent.iteratedFDeriv ℝ k).self_of_nhds)).trans
      (by simpa only [map_zero, add_zero] using ha)

/-- Angular differentiation may also be performed after evaluating the
parameter jet. The slot order is preserved without diagonalization. -/
theorem n04NegativeChart_finiteRepresentative_parameterAngularJet
    {U : Set E} {g : E × ℝ → ℝ} {h : P × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) g)
    (Ja : ∀ b : ℕ, ∀ θ : ℝ, SmoothDirections U
      (fun z => iteratedDeriv b (fun η => g (z, η)) θ))
    {V : Set P} (hV : IsOpen V) (h0 : (0 : P) ∈ V)
    (x : E) (hx : x ∈ U) (L : P →L[ℝ] E)
    (heq : ∀ y ∈ V, ∀ θ, h (y, θ) = g (x + L y, θ))
    (k b : ℕ) (θ : ℝ) (v : Fin k → P) :
    iteratedDeriv b (fun η => iteratedFDeriv ℝ k (fun y => h (y, η)) 0 v) θ =
      (Ja b θ).D k x (fun i => L (v i)) := by
  have he (η : ℝ) : iteratedFDeriv ℝ k (fun y => h (y, η)) 0 v =
      (Ja 0 η).D k x (fun i => L (v i)) := by
    simpa only [iteratedDeriv_zero] using
      n04NegativeChart_finiteRepresentative_angularJet hV h0 x hx L heq 0 η (Ja 0 η) k v
  rw [show (fun η => iteratedFDeriv ℝ k (fun y => h (y, η)) 0 v) =
      (fun η => (Ja 0 η).D k x (fun i => L (v i))) from funext he]
  exact iteratedDeriv_stateJet_angle (Ja 0 0).open_domain
    (isFiniteAffineTimeSmooth_of_jointSmoothDirections J)
    (fun b q => Ja b q.2) b k hx (0 : ℝ) θ (fun i => L (v i))

/-- Removing the initial angle is a fixed continuous linear operation. -/
def n04NegativeChart_jointLabelDisplacement
    {U : Set E} {g : E × ℝ → ℝ}
    (J : SmoothDirections (U ×ˢ (univ : Set ℝ)) g) :
    SmoothDirections (U ×ˢ (univ : Set ℝ)) (fun p => g p - p.2) := by
  let K := smoothDirectionsLinearOn (ContinuousLinearMap.snd ℝ E ℝ) J.open_domain
  let D : (ℝ × ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  exact (solveSmoothDirectionsPostcomp (smoothDirectionsProd J K) D).congrOn
    (fun _ _ => by simp only [D, Function.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'])

namespace N04RealizationStart

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

set_option backward.isDefEq.respectTransparency true

variable (W : N04RealizationStart)

/-- A genuine globally smooth representative of the literal root label
on a finite state plot, with one common neighbourhood for all angles. -/
theorem negativeRootLabel_finiteRepresentative
    (z : Parameter W.S) (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    (L : P →L[ℝ] Parameter W.S) (m : ℕ) (side : Bool) :
    ∃ h : P × ℝ → ℝ, ContDiff ℝ ∞ h ∧
      ∃ V : Set P, IsOpen V ∧ (0 : P) ∈ V ∧
        (∀ y ∈ V, z + L y ∈ sectorNeighborhood W.S W.base W.ε W.ε) ∧
        ∀ y ∈ V, ∀ θ, h (y, θ) =
          n01RootLabel W.S W.C (liftSectorParameter W.S W.C (z + L y)) m side θ :=
  n04NegativeChart_finiteStateAngle_representative
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
    (n04Realization_rootLabel_forwardJointDirections W.hT W.hS W.through03.1.1 m side)
    z hz L

/-- The angular-then-state jets of the represented displacement are the
actual scalar jets used by `negativeRootLabel_angular_prefix`. -/
theorem negativeRootLabel_finiteRepresentative_angularJet
    (z : Parameter W.S) (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    (L : P →L[ℝ] Parameter W.S) (m : ℕ) (side : Bool)
    {h : P × ℝ → ℝ} {V : Set P} (hV : IsOpen V) (h0 : (0 : P) ∈ V)
    (heq : ∀ y ∈ V, ∀ θ, h (y, θ) =
      n01RootLabel W.S W.C (liftSectorParameter W.S W.C (z + L y)) m side θ)
    (b : ℕ) (θ : ℝ)
    (Ja : SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε)
      (fun x => iteratedDeriv b
        (fun η => n01RootLabel W.S W.C (liftSectorParameter W.S W.C x) m side η - η) θ))
    (k : ℕ) (v : Fin k → P) :
    iteratedFDeriv ℝ k (fun y => iteratedDeriv b (fun η => h (y, η) - η) θ) 0 v =
      Ja.D k z (fun i => L (v i)) :=
  n04NegativeChart_finiteRepresentative_angularJet
    (g := fun p => n01RootLabel W.S W.C (liftSectorParameter W.S W.C p.1) m side p.2 - p.2)
    (h := fun p => h p - p.2) hV h0 z hz L
    (fun y hy θ => congrArg (fun a : ℝ => a - θ) (heq y hy θ)) b θ Ja k v

/-- The reverse derivative order has the same original multilinear
slots, including zero state and zero angular orders. -/
theorem negativeRootLabel_finiteRepresentative_parameterAngularJet
    (z : Parameter W.S) (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    (L : P →L[ℝ] Parameter W.S) (m : ℕ) (side : Bool)
    {h : P × ℝ → ℝ} {V : Set P} (hV : IsOpen V) (h0 : (0 : P) ∈ V)
    (heq : ∀ y ∈ V, ∀ θ, h (y, θ) =
      n01RootLabel W.S W.C (liftSectorParameter W.S W.C (z + L y)) m side θ)
    (Ja : ∀ b : ℕ, ∀ θ : ℝ,
      SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε)
        (fun x => iteratedDeriv b
          (fun η => n01RootLabel W.S W.C (liftSectorParameter W.S W.C x) m side η - η) θ))
    (k b : ℕ) (θ : ℝ) (v : Fin k → P) :
    iteratedDeriv b (fun η => iteratedFDeriv ℝ k (fun y => h (y, η) - η) 0 v) θ =
      (Ja b θ).D k z (fun i => L (v i)) :=
  n04NegativeChart_finiteRepresentative_parameterAngularJet
    (h := fun p => h p - p.2)
    (n04NegativeChart_jointLabelDisplacement
      (n04Realization_rootLabel_forwardJointDirections W.hT W.hS W.through03.1.1 m side))
    Ja hV h0 z hz L (fun y hy θ => congrArg (fun a : ℝ => a - θ) (heq y hy θ)) k b θ v

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootLabel_finiteRepresentative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootLabel_finiteRepresentative

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootLabel_finiteRepresentative_parameterAngularJet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootLabel_finiteRepresentative_parameterAngularJet
