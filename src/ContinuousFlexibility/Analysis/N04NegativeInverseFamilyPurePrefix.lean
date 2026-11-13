import ContinuousFlexibility.Analysis.N04NegativeInverseFiniteFamily
import ContinuousFlexibility.Analysis.N04NegativeInverseForwardBounds

/-!
# Uniform pure prefixes for finite families of actual negative atoms

A finite selector uses one low base before the parameter prefix and one
shift before the spatial order. The conversion to the genuine joint
towers preserves the parameter and spatial arities. Its spatial factor
is absorbed into a single material envelope for the whole family.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

/-- All atoms selected by a finite family share the same exact joint
prefix estimate, including its low base, shift and material envelope. -/
theorem negativeInverse_atomFamily_purePrefix
    {A : Type*} [Fintype A] {b : ℕ} {ε : ℝ}
    (select : A → Atom) (hselect : ∀ a, atomIsGeometry (select a))
    (h : ∀ a, G.Data 0 (G.Neg 0) b ε
      (G.atomFamily 0 (select a)) (G.atomRef 0 (select a))) :
    ∃ low : ℕ, b ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ, 1 ≤ shift ∧ ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ a m (hm : G.Neg 0 m),
        ∀ J : SmoothDirections (sectorNeighborhood G.W.S b ε ε ×ˢ unitStrip)
          (fun x : Parameter G.W.S × PolarPoint => G.atomFamily 0 (select a) x.1 m x.2),
        ∀ z ∈ sectorNeighborhood G.W.S b ε ε, parameterGrading G.W.S low z ≤ 1 →
        ∀ q ∈ unitStrip, ∀ n : ℕ, ∀ w : StateAngleWord n,
          w.stateArity ≤ K → w.angleArity ≤ s →
        ∀ v : Fin n → Parameter G.W.S × PolarPoint,
          (∀ i, parameterGrading G.W.S low (v i).1 ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → parameterGrading G.W.S (low + s + shift * K + 1) z ≤ R →
          (∀ i, parameterGrading G.W.S (low + s + shift * K + 1) (v i).1 ≤ R) →
          (∀ i, ‖(v i).2‖ ≤ 1) →
          (∀ i, w.isState i = false → (v i).1 = 0) →
          (∀ i, w.isState i = true → (v i).2 = 0) →
        |J.D n (z, q) v| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V 0).cell m)) ^ B *
            parameterHeightWeight
              (G.W.U.H (G.W.U.sample ((G.V 0).cell m)) ^ (3 / 4 : ℝ)) w.stateArity *
            R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
              (((s + shift * K : ℕ) : ℝ) + 1)) := by
  have hU := isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT
  have href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ a m, G.Neg 0 m →
      ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (G.atomRef 0 (select a) m) q| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V 0).cell m)) ^ B := by
    intro s
    let reference := G.negativeInverse_reference_geometry_bounds s
    let B : ℝ := reference.choose
    have hB : 0 < B := reference.choose_spec.1
    have hb := reference.choose_spec.2
    exact ⟨B, hB, fun a m hm q hq i j hij =>
      hb 0 m hm (select a) (hselect a) q hq i j hij⟩
  let prefixData :=
    CurrentJetDataOn.negativeInverse_finiteFamily_sharpPrefix_power
      (A := A) (D := G.W.D) (S := G.S 0) (T := G.W.U) (cell := (G.V 0).cell)
      (P := G.Neg 0) (base := b) (ε := ε)
      (f := fun a => G.atomFamily 0 (select a))
      (f₀ := fun a => G.atomRef 0 (select a))
      G.W.radial.1 hU G.W.negativeInverse_parameterInterpolation h
      (fun a m hm =>
        (G.negativeInverse_reference_geometry_regular 0 m hm (select a) (hselect a)).1)
      href (G.cost_nonneg 0).2.2 (G.cost_nonneg 0).2.1
  let low : ℕ := prefixData.choose
  refine ⟨low, prefixData.choose_spec.1, fun K => ?_⟩
  let shiftData := prefixData.choose_spec.2 K
  let shift : ℕ := shiftData.choose
  refine ⟨shift, shiftData.choose_spec.1, fun s => ?_⟩
  let bound := shiftData.choose_spec.2 s
  let C : ℝ := bound.choose
  have hC : 0 < C := bound.choose_spec.1
  let packed := coefficientEnvelope_pack ((2 : ℝ) ^ s * C) C
  let B : ℝ := packed.choose
  have hB : 0 < B := packed.choose_spec.1
  have hpack := packed.choose_spec.2
  refine ⟨B, hB, ?_⟩
  intro a m hm J z hz hzlow q hq n w hwK hws v hvlow R hR hzR hvR hvphys hvstate hvspatial
  let E := G.W.U.E0 (G.W.U.sample ((G.V 0).cell m))
  let H := G.W.U.H (G.W.U.sample ((G.V 0).cell m)) ^ (3 / 4 : ℝ)
  let major : ℕ → ℕ → ℝ := fun k t =>
    C * E ^ C * parameterHeightWeight H k *
      R ^ (((t + shift * k - 1 : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))
  have hE : 1 ≤ E := (G.cost_nonneg 0).2.2 m
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg 0).2.1 m) _
  have hmajor (k t : ℕ) : 0 ≤ major k t :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le
      (Real.rpow_nonneg (zero_le_one.trans hE) _))
      (parameterHeightWeight_nonneg hH k))
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hraw := n04NegativeInverse_pureJoint_of_parameterTowers
    (E := Parameter G.W.S) (U := sectorNeighborhood G.W.S b ε ε) (V := unitStrip)
    (f := fun x : Parameter G.W.S × PolarPoint => G.atomFamily 0 (select a) x.1 m x.2)
    (sectorNeighborhood_isOpen G.W.S b ε ε) (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex G.W.S b ε ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))
    (parameterGrading G.W.S low)
    (parameterGrading G.W.S (low + s + shift * K + 1)) R z hz q hq w J major hmajor
    (fun k i j hk hij Q u hu huR =>
      bound.choose_spec.2 a k (hk.trans hwK) m hm q hq i j (hij.trans hws)
        Q z hz hzlow u hu R hR hzR huR)
    v hvlow hvR hvphys hvstate hvspatial
  have htwo : (2 : ℝ) ^ w.angleArity ≤ (2 : ℝ) ^ s :=
    pow_le_pow_right₀ (by norm_num) hws
  have hcost : (2 : ℝ) ^ w.angleArity * (C * E ^ C) ≤ B * E ^ B := by
    calc
      _ ≤ (2 : ℝ) ^ s * (C * E ^ C) :=
        mul_le_mul_of_nonneg_right htwo
          (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hE) _))
      _ = ((2 : ℝ) ^ s * C) * E ^ C := (mul_assoc _ _ _).symm
      _ ≤ B * E ^ B := hpack E hE
  have htail : 0 ≤ parameterHeightWeight H w.stateArity *
      R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
        (((s + shift * K : ℕ) : ℝ) + 1)) :=
    mul_nonneg (parameterHeightWeight_nonneg hH _)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  calc
    |J.D n (z, q) v| ≤ (2 : ℝ) ^ w.angleArity * major w.stateArity w.angleArity := hraw
    _ = ((2 : ℝ) ^ w.angleArity * (C * E ^ C)) *
        (parameterHeightWeight H w.stateArity *
          R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1))) := by simp only [major, mul_assoc]
    _ ≤ (B * E ^ B) * (parameterHeightWeight H w.stateArity *
        R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1))) := mul_le_mul_of_nonneg_right hcost htail
    _ = _ := (mul_assoc _ _ _).symm


end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_atomFamily_purePrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_atomFamily_purePrefix
