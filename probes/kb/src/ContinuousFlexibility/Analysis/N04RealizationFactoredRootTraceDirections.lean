import ContinuousFlexibility.Analysis.N04RealizationPhysicalRootJetDirections
import ContinuousFlexibility.Analysis.N06BoundaryRadialJets
import ContinuousFlexibility.Analysis.N06RootPhysicalFiniteJets
import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# Actual inward root traces and the fixed reference speed factor

The radial affine change is evaluated through its genuine spatial jet.
The speed factor is the existing reference factor, whose ordinary jets
are independent of the state. Finite Leibniz sums preserve the same
state-angle neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

private theorem radialJet_shift
    {f : PolarPoint → ℝ} {r σ θ : ℝ} (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f (r, θ)) :
    radialBoundaryJet (fun p => f (rootProfileShift r σ p)) 0 n θ =
      iteratedFDeriv ℝ n f (r, θ) (fun _ => (σ, 0)) := by
  let L : ℝ →L[ℝ] PolarPoint :=
    (σ • ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)
  let g : PolarPoint → ℝ := fun p => f (p + (r, θ))
  have hpoint : L 0 + (r, θ) = (r, θ) := by
    rw [L.map_zero, zero_add]
  have hg : ContDiffAt ℝ (n : ℕ∞ω) g (L 0) :=
    (show ContDiffAt ℝ (n : ℕ∞ω) f (L 0 + (r, θ)) by
      rw [hpoint]
      exact hf.of_le (by simp)).comp (L 0) (contDiffAt_id.add contDiffAt_const)
  have he := congrArg
    (fun A : (ℝ [×n]→L[ℝ] ℝ) => A (fun _ => 1))
    (n06_iteratedFDeriv_compCLM_at L n hg)
  have hslice : g ∘ L = fun x : ℝ => f (rootProfileShift r σ (x, θ)) := by
    funext x
    have h1 : g (L x) = f (σ * x + r, θ) := by
      simp only [g, L, ContinuousLinearMap.prod_apply,
        smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
        smul_eq_mul, Prod.mk_add_mk, zero_add]
    rw [Function.comp_apply, h1]
    simp only [rootProfileShift, add_comm]
  rw [hslice, ContinuousMultilinearMap.compContinuousLinearMap_apply] at he
  have hshift : iteratedFDeriv ℝ n g (L 0) = iteratedFDeriv ℝ n f (r, θ) := by
    change iteratedFDeriv ℝ n (fun p => f (p + (r, θ))) (L 0) = _
    rw [iteratedFDeriv_comp_add_right, hpoint]
  rw [hshift] at he
  simpa only [radialBoundaryJet, iteratedDeriv_eq_iteratedFDeriv, L,
    ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
    smul_eq_mul, mul_one] using he

/-- Actual inward normal traces of each physical root coefficient. -/
def n04Realization_orientedRootFieldTrace_joint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (σ : ℝ) (π : PolarPoint →L[ℝ] ℝ) (n : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z : (StateDirections S × ℝ) × ℝ =>
        radialBoundaryJet
          (fun p => π (n06PhysicalRootFields D S C
            (liftSectorParameter S C z.1) (rootProfileShift r σ p))) 0 n z.2) := by
  apply (n04Realization_physicalRootJet_joint hT hS hN hε hr hroot
    π n (fun _ => (σ, 0))).congr
  intro z hz
  exact (radialJet_shift n (π.contDiff.contDiffAt.comp (r, z.2)
    (n06_physicalRootFields_contDiffAt_root hT hS hN
      (liftSectorParameter_mem_stateNeighborhood hz.1 le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z.1) hr hroot z.2))).symm

private def fixedRadialProductTrace
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set (X × ℝ)} {f : X → PolarPoint → ℝ} {a : ℝ → ℝ}
    (hU : IsOpen U) (ha : ContDiffAt ℝ ∞ a 0)
    (hf : ∀ z ∈ U, ContDiffAt ℝ ∞ (fun x => f z.1 (x, z.2)) 0)
    (J : ∀ j : ℕ, SmoothDirections U (fun z => radialBoundaryJet (f z.1) 0 j z.2))
    (n : ℕ) :
    SmoothDirections U
      (fun z => radialBoundaryJet (fun p => a p.1 * f z.1 p) 0 n z.2) := by
  let K (i : Fin (n + 1)) : SmoothDirections U
      (fun z => (n.choose i : ℝ) * iteratedDeriv i a 0 *
        radialBoundaryJet (f z.1) 0 (n - i) z.2) :=
    smoothDirections_realConstMul
      ((n.choose i : ℝ) * iteratedDeriv i a 0) (J (n - i))
  apply (smoothDirections_finiteSum hU K).congr
  intro z hz
  change (∑ i : Fin (n + 1), (n.choose i : ℝ) * iteratedDeriv i a 0 *
    iteratedDeriv (n - i) (fun x => f z.1 (x, z.2)) 0) =
      iteratedDeriv n (fun x => a x * f z.1 (x, z.2)) 0
  exact (Fin.sum_univ_eq_sum_range (fun i => (n.choose i : ℝ) * iteratedDeriv i a 0 *
    iteratedDeriv (n - i) (fun x => f z.1 (x, z.2)) 0) (n + 1)).trans (iteratedDeriv_fun_mul
    (ha.of_le (show (n : ℕ∞ω) ≤ ∞ by simp))
    ((hf z hz).of_le (show (n : ℕ∞ω) ≤ ∞ by simp))).symm

/-- The literal factored speed has genuine boundary trace towers for any
one fixed smooth reference division factor supplied by the root strip. -/
def n04Realization_factoredRootSpeedTrace_joint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (σ : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : 0 < g 0) (n : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (fun z : (StateDirections S × ℝ) × ℝ =>
        radialBoundaryJet
          (factoredCharacteristicSpeed D.w g
            (stateProfile D S C (liftSectorParameter S C z.1).1)
            (stateHeight D S C (liftSectorParameter S C z.1)) r σ) 0 n z.2) := by
  let U : Set ((StateDirections S × ℝ) × ℝ) :=
    sectorNeighborhood S base ε ε ×ˢ univ
  let f : (StateDirections S × ℝ) → PolarPoint → ℝ := fun z p =>
    (n06PhysicalRootFields D S C (liftSectorParameter S C z)
      (rootProfileShift r σ p)).2
  let a : ℝ → ℝ := referenceRootSpeedFactor D.w g r σ
  have hU : IsOpen U := (isOpen_sectorNeighborhood S base ε ε).prod isOpen_univ
  have hw : ContDiff ℝ ∞ D.w := hN.1.1.choose_spec.1.2.2.1.1
  have hrpos : 0 < r + σ * 0 := by
    simpa only [mul_zero, add_zero] using hN.1.1.choose_spec.1.1.trans hr.1
  have hwpos : 0 < D.w (r + σ * 0) := by
    simpa only [mul_zero, add_zero] using hN.1.1.choose_spec.1.2.2.2.2.1 r hr
  have ha : ContDiffAt ℝ ∞ a 0 :=
    contDiffAt_referenceRootSpeedFactor hw hg hrpos hwpos hg0
  have hf (z : (StateDirections S × ℝ) × ℝ) (hz : z ∈ U) :
      ContDiffAt ℝ ∞ (fun x => f z.1 (x, z.2)) 0 := by
    have h := (n06_physicalRootFields_contDiffAt_root hT hS hN
      (liftSectorParameter_mem_stateNeighborhood hz.1 le_rfl)
      (hN.2.2.1.liftSectorParameter_sector z.1) hr hroot z.2).snd
    have hshift : ContDiffAt ℝ ∞
        (fun x : ℝ => ((r + σ * x, z.2) : PolarPoint)) 0 :=
      (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).prodMk contDiffAt_const
    have h' : ContDiffAt ℝ ∞
        (fun p => (n06PhysicalRootFields D S C (liftSectorParameter S C z.1) p).2)
        (r + σ * 0, z.2) := by
      simpa only [mul_zero, add_zero] using h
    simpa only [f, rootProfileShift, Function.comp_def] using h'.comp 0 hshift
  let J (j : ℕ) : SmoothDirections U (fun z => radialBoundaryJet (f z.1) 0 j z.2) :=
    n04Realization_orientedRootFieldTrace_joint hT hS hN hε hr hroot σ
      (ContinuousLinearMap.snd ℝ ℝ ℝ) j
  apply (fixedRadialProductTrace hU ha hf J n).congr
  intro z hz
  have hwline : ContinuousAt (fun x : ℝ => D.w (r + σ * x)) 0 :=
    hw.continuous.continuousAt.comp
      ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt)
  have hnear : ∀ᶠ x : ℝ in 𝓝 0, 0 < D.w (r + σ * x) :=
    hwline.eventually (Ioi_mem_nhds hwpos)
  have he : (fun x => a x * f z.1 (x, z.2)) =ᶠ[𝓝 0]
      (fun x => factoredCharacteristicSpeed D.w g
        (stateProfile D S C (liftSectorParameter S C z.1).1)
        (stateHeight D S C (liftSectorParameter S C z.1)) r σ (x, z.2)) := by
    filter_upwards [hnear] with x hx
    exact (n06_factoredRootFields_eq_physical D S C
      (liftSectorParameter S C z.1) g r σ (x, z.2) hx.ne').2.symm
  exact Filter.EventuallyEq.iteratedDeriv_eq n he

end ContinuousFlexibility.Analysis
