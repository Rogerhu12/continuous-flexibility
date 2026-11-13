import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsBoundaryInputPrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryBoundaryFormulaPrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledSampleHeight

/-!
# Sampled mixed prefixes of the eight actual root formulas

The finite differential recursion keeps one intrinsic angular order
in reserve. Its true parameter towers retain one complete sample height
factor at every positive parameter order, at one low base selected
before all finite parameter prefixes.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04BoundaryFormulaPrefixStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

def n04PositiveGeometry_rootBoundaryFormula
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (g : ℝ → ℝ) (m : ℕ) (side : Bool) (j : Fin 8)
    (y : (StateDirections S × ℝ) × ℝ) : ℝ :=
  n04PositiveGeometry_boundaryFormula j
    (fun l θ => n04PositiveGeometry_rootBoundaryInput D S C g m side l (y.1, θ)) y.2

def n04PositiveGeometry_rootBoundaryFormula_joint
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hg0 : 0 < g 0)
    (m : ℕ) (side : Bool) (hr : n01ComponentRoot C m side ∈ radialCore D)
    (hroot : deriv D.w (n01ComponentRoot C m side) = 0) (j : Fin 8) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (n04PositiveGeometry_rootBoundaryFormula D S C g m side j) :=
  n04PositiveGeometry_boundaryFormula_directions
    (n04PositiveGeometry_rootBoundaryInput_joint hT hS hN hε g hg hg0 m side hr hroot) j

theorem n04PositiveGeometry_rootBoundaryFormula_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → 0 < g 0 →
      (∀ t, -deriv W.D.w (n01ComponentRoot W.C m (!side) +
        n01ComponentRootOrientation (!side) * t) = t * g t) →
      ∀ ρ : ℝ, 0 < ρ →
      RootCoefficientStripConditions W.D.w g
        (stateProfile W.D W.S W.C W.C.referenceState)
        (stateHeight W.D W.S W.C (W.C.referenceState, 0))
        (n01ComponentRoot W.C m (!side)) (n01ComponentRootOrientation (!side)) ρ →
      ∀ j : Fin 8, ∀ k : ℕ, k ≤ K → ∀ u : ℕ, u ≤ s → ∀ d : ℕ, d ≤ 1 →
      ∀ θ : ℝ, ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun z => iteratedDeriv (u + d)
          (fun η => n04PositiveGeometry_rootBoundaryFormula W.D W.S W.C g m (!side) j
            (z, η)) θ),
      ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 →
      ∀ v : Fin k → (StateDirections W.S × ℝ),
      (∀ l, pairGrading (sectorGrading W.S) realGrading low (v l) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      (∀ l, pairGrading (sectorGrading W.S) realGrading
        (low + s + shift * K + 1) (v l) ≤ R) →
      ‖J.D k z v‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k *
        R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  refine (n04PositiveGeometry_rootBoundaryInput_sample_prefix
    W X hb hε hεW hεone hflow).elim fun low h => ?_
  refine h.elim fun hlow hprefix => ?_
  obtain ⟨RH, hRH, hheight⟩ := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let L := max 1 RH
  have hL : 1 ≤ L := le_max_left _ _
  refine ⟨low, hlow, fun K => ?_⟩
  refine (hprefix K).elim fun shift hshift => ?_
  refine ⟨shift, fun s => ?_⟩
  refine (hshift s).elim fun Ai h => ?_
  refine h.elim fun hAi hin => ?_
  refine (n04PositiveGeometry_boundaryFormulas_weighted_reserve
    (E := StateDirections W.S × ℝ) K s 1 L hL).elim fun C h => ?_
  refine h.elim fun hC h => ?_
  refine h.elim fun degree hformula => ?_
  obtain ⟨A₀, _, hpack⟩ := coefficientEnvelope_pack (C * Ai ^ degree) (Ai * degree)
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  have hA₀A : A₀ ≤ A := le_max_right _ _
  refine ⟨A, hA, ?_⟩
  intro i side m hm g hg hg0 hfactor ρ hρ hstrip j k hk u hu d hd θ J z hz hzlow v hv R hR hzR hvR
  let E : ℝ := W.U.E0 (W.U.sample (X.cell i))
  let H : ℝ := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let M : ℝ := Ai * E ^ Ai
  let t : ℝ := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P : (StateDirections W.S × ℝ) → Prop := fun w =>
    pairGrading (sectorGrading W.S) realGrading low w ≤ 1 ∧
    pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) w ≤ R
  have hP : P 0 := by
    constructor
    · simpa only [map_zero] using (show (0 : ℝ) ≤ 1 from zero_le_one)
    · simpa only [map_zero] using (zero_le_one.trans hR)
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (hheight i).1
  have hHL : H ≤ L := (hheight i).2.trans (le_max_right _ _)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hAi
    (Real.one_le_rpow hE (zero_le_one.trans hAi))
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have htpow (n : ℕ) : t ^ n =
      R ^ ((n : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hR)]
    congr 1
    ring
  have hrad : n01ComponentRoot W.C m (!side) = n04PositiveEndpoint i side := by
    have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact he.symm
  have hr : n01ComponentRoot W.C m (!side) ∈ radialCore W.D := by
    rw [hrad]
    exact (W.roots i side).1
  have hroot : deriv W.D.w (n01ComponentRoot W.C m (!side)) = 0 := by
    rw [hrad]
    exact (W.roots i side).2.1
  let Ji := n04PositiveGeometry_rootBoundaryInput_joint
    W.hT W.hS hN hεone g hg hg0 m (!side) hr hroot
  have hsource (l : Fin 9) (e : ℕ) (he : e ≤ K) (b : ℕ) (hb : b ≤ s)
      (a : ℕ) (ha : a ≤ 1 + 3)
      (Q : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun y => iteratedDeriv (b + a)
          (fun η => n04PositiveGeometry_rootBoundaryInput W.D W.S W.C g m (!side) l
            (y, η)) θ))
      (w : Fin e → (StateDirections W.S × ℝ)) (hw : ∀ l, P (w l)) :
      ‖Q.D e z w‖ ≤ M * parameterHeightWeight H e * t ^ (b + shift * e) := by
    rw [htpow]
    exact hin i side m hm g hg hg0 hfactor ρ hρ hstrip l e he b hb a ha θ Q
      z hz hzlow w (fun l => (hw l).1) R hR hzR (fun l => (hw l).2)
  have hout := hformula (sectorNeighborhood_convex W.S base ε ε) Ji
    z hz θ P hP M H t hM hH hHL ht shift hsource
    j k hk u hu d hd J v (fun l => ⟨hv l, hvR l⟩)
  have hcost : C * M ^ degree ≤ A * E ^ A := by
    calc
      _ = (C * Ai ^ degree) * E ^ (Ai * degree) := by
        dsimp only [M]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE)]
        ring
      _ ≤ A₀ * E ^ A₀ := hpack E hE
      _ ≤ A * E ^ A := mul_le_mul hA₀A
        (Real.rpow_le_rpow_of_exponent_le hE hA₀A)
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)
  rw [htpow] at hout
  exact hout.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcost (parameterHeightWeight_nonneg hH k))
      (Real.rpow_nonneg (zero_le_one.trans hR) _))

end ContinuousFlexibility.Analysis
