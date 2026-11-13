import ContinuousFlexibility.Analysis.N04NegativeInverseGeometry
import ContinuousFlexibility.Analysis.N04NegativeInverseMixedPrefix

/-!
# The two actual inverse atoms from the vector inverse point

Radial normalization is a fixed affine output map. The angular defect
subtracts the original canonical angle; its derivative vanishes on
every positive-parameter pure tuple. These identities retain the exact
inverse point and require no estimates for inverse atoms as input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements CanonicalGeometry
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04NegativeInverse_affineRadial_jet
    {U : Set E} {F : E → PolarPoint} (J : SmoothDirections U F)
    (left span : ℝ) (K : SmoothDirections U (fun x => ((F x).1 - left) / span))
    {n : ℕ} (hn : 0 < n) {x : E} (hx : x ∈ U) (v : Fin n → E) :
    K.D n x v = (J.D n x v).1 / span := by
  let L : PolarPoint →L[ℝ] ℝ := span⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ
  let A := smoothDirections_postcompCLM J L
  let K' : SmoothDirections U (fun x => (L ∘ F) x - left / span) :=
    K.congrOn (fun x _ => by
      simp only [L, Function.comp_apply, smul_apply, ContinuousLinearMap.coe_fst',
        smul_eq_mul, div_eq_mul_inv]
      ring)
  have he := smoothDirections_D_sub_constant A K' hn hx v
  change K.D n x v = _ at he
  rw [smoothDirections_postcompCLM_D_apply] at he
  simpa only [L, smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
    div_eq_mul_inv, mul_comm] using he

theorem n04NegativeInverse_angleDefect_jet
    {U : Set (E × PolarPoint)} {F : E × PolarPoint → PolarPoint}
    (J : SmoothDirections U F)
    (K : SmoothDirections U (fun x => (F x).2 - x.2.2))
    {n : ℕ} (w : StateAngleWord n) (hκ : 0 < w.stateArity)
    {x : E × PolarPoint} (hx : x ∈ U) (v : Fin n → E × PolarPoint)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    K.D n x v = (J.D n x v).2 := by
  let L : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let T := smoothDirectionsOfJets J.open_domain (continuousLinearJets L)
    (hasProjectiveJetsOn_continuousLinear L U)
  have hzero : T.D n x v = 0 := by
    change continuousLinearJets L n x v = 0
    cases n with
    | zero =>
        cases w
        exact (Nat.lt_irrefl 0 hκ).elim
    | succ n =>
        cases n with
        | zero =>
            simp only [continuousLinearJets,
              ContinuousMultilinearMap.ofSubsingleton_apply_apply]
            change (v 0).2.2 = 0
            cases w with
            | state u => exact congrArg Prod.snd (hspatial 0 rfl)
            | angle u =>
                cases u
                exact (Nat.lt_irrefl 0 hκ).elim
        | succ n => simp only [continuousLinearJets, ContinuousMultilinearMap.zero_apply]
  let A : SmoothDirections U (fun x => (F x).2) :=
    (smoothDirections_postcompCLM J (ContinuousLinearMap.snd ℝ ℝ ℝ)).congrOn
      (fun _ _ => rfl)
  let B : SmoothDirections U (fun x => (F x).2) :=
    (smoothDirectionsAdd K T).congrOn (fun x _ => by
      change (F x).2 - x.2.2 + x.2.2 = (F x).2
      exact sub_add_cancel _ _)
  have he := congrArg (fun Q : (E × PolarPoint) [×n]→L[ℝ] ℝ => Q v) (B.unique A n x hx)
  change K.D n x v + T.D n x v =
    (smoothDirections_postcompCLM J (ContinuousLinearMap.snd ℝ ℝ ℝ)).D n x v at he
  simpa only [hzero, add_zero, smoothDirections_postcompCLM_D_apply,
    ContinuousLinearMap.coe_snd'] using he

/-- Scalar coordinate estimates are proved before the atlas is supplied. -/
private theorem negativeInverse_radial_norm_le (p : PolarPoint) (span : ℝ)
    {r : ℝ} (hr : r = p.1 / span) :
    |r| ≤ (1 + |span⁻¹|) * ‖p‖ := by
  rw [hr, abs_div]
  have hp : |p.1| ≤ ‖p‖ := by
    simpa only [Real.norm_eq_abs] using norm_fst_le p
  calc
    _ = |span⁻¹| * |p.1| := by rw [abs_inv, div_eq_mul_inv, mul_comm]
    _ ≤ |span⁻¹| * ‖p‖ := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg p)

private theorem negativeInverse_angular_norm_le (p : PolarPoint) (span : ℝ)
    {r : ℝ} (hr : r = p.2) :
    |r| ≤ (1 + |span⁻¹|) * ‖p‖ := by
  rw [hr]
  have hp : |p.2| ≤ ‖p‖ := by
    simpa only [Real.norm_eq_abs] using norm_snd_le p
  exact hp.trans (le_mul_of_one_le_left (norm_nonneg p)
    (le_add_of_nonneg_right (abs_nonneg _)))

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

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- The actual inverse point of a canonical unit point, before taking
its normalized radial or angular-defect component. -/
def negativeInversePointJointTower
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m) :
    SmoothDirections (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε ×ˢ unitStrip)
      (fun x : Parameter G.W.S × PolarPoint => G.pulledPoint η (G.lift η x.1) m x.2) := by
  let data : ∃ j : ℕ × Bool, G.e m = .inl j := (G.neg_iff_inl η m).mp hm
  let j : ℕ × Bool := data.choose
  have hi : G.e m = .inl j := data.choose_spec
  let k := G.negativeIndex j
  have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  apply (n04NegativeInverse_canonicalUnitJointTower (G.W.A G.X.e₀) k
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε)
    (G.W.negativeInverseJointTower j.1 j.2)
    (G.W.negativeCanonicalUnit_mapsTo G.X.e₀ k j.1 j.2 hk)).congrOn
  intro x hx
  have hf := n04bTypedAtlasData_negative_fields
    (C := G.W.C) (L := G.W.L) (z := liftSectorParameter G.W.S G.W.C x.1) G.X.e₀
    (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualReferenceCut G.W.through03) k j.1 j.2 hk
  have hinverse : (G.W.A G.X.e₀).inverseChart
      (liftSectorParameter G.W.S G.W.C x.1) k =
      n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C x.1) j.1 j.2 := hf.2.2.2.2.1
  exact ((G.negative_pulledPoint η (G.lift η x.1) m j hi x.2).trans
    (congrFun hinverse (canonicalUnitPoint (G.W.A G.X.e₀) k x.2))).symm

/-- The two normalized atoms inherit the vector inverse estimate on
every pure tuple containing an original parameter slot. -/
theorem negativeInverseAtom_positiveJoint_bound
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {U : Set (Parameter G.W.S × PolarPoint)} (m : ℕ)
    (J : SmoothDirections U
      (fun x : Parameter G.W.S × PolarPoint => G.pulledPoint η (G.lift η x.1) m x.2))
    (a : Atom) (ha : atomIsNegativeInverse a)
    (K : SmoothDirections U
      (fun x : Parameter G.W.S × PolarPoint => G.atomFamily η a x.1 m x.2))
    {n : ℕ} (w : StateAngleWord n) (hκ : 0 < w.stateArity)
    {x : Parameter G.W.S × PolarPoint} (hx : x ∈ U)
    (v : Fin n → Parameter G.W.S × PolarPoint)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0) :
    |K.D n x v| ≤ (1 + |((G.V η).physicalRight m - (G.V η).physicalLeft m)⁻¹|) *
      ‖J.D n x v‖ := by
  have hn : 0 < n := by have hs := w.arity_sum; omega
  cases a <;> simp only [atomIsNegativeInverse] at ha
  · have he := n04NegativeInverse_affineRadial_jet J ((G.V η).physicalLeft m)
        ((G.V η).physicalRight m - (G.V η).physicalLeft m) K hn hx v
    exact negativeInverse_radial_norm_le (J.D n x v)
      ((G.V η).physicalRight m - (G.V η).physicalLeft m) he
  · have he := n04NegativeInverse_angleDefect_jet J K w hκ hx v hspatial
    exact negativeInverse_angular_norm_le (J.D n x v)
      ((G.V η).physicalRight m - (G.V η).physicalLeft m) he

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverseAtom_positiveJoint_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverseAtom_positiveJoint_bound
