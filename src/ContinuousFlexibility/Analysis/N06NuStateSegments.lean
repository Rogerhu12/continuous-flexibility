import ContinuousFlexibility.Analysis.N06NuCoordinateBounds
import ContinuousFlexibility.Analysis.N05ReferenceResidual

/-!
# The actual state segments for nu-column estimates

The original neighborhood and sector contain the line from the actual
reference state to the current state. The finite physical nu coordinates
carry that line to the literal straight segment in finite-dimensional
coordinate space. N01 therefore supplies the discriminant lower bound
all along the finite segment used by the mean value estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/- Cache the original product module instances. In particular, elaborating
an affine state expression must not search through the realizations of the
Sobolev and circle projective limits. These are the existing instances. -/
local instance n06NuHeightModule (S : PhysicalSpacesData) :
    Module ℝ (S.height (3 / 4 : ℝ)).Space := inferInstance

local instance n06NuCircleModule (S : PhysicalSpacesData) :
    Module ℝ (CircleSpace S) := inferInstance

local instance n06NuHeightPairModule (S : PhysicalSpacesData) :
    Module ℝ (HeightPair S) := Prod.instModule

local instance n06NuCirclePairModule (S : PhysicalSpacesData) :
    Module ℝ (CircleSpace S × CircleSpace S) := Prod.instModule

local instance n06NuControlsModule (S : PhysicalSpacesData) :
    Module ℝ (ℝ × (CircleSpace S × CircleSpace S)) := Prod.instModule

local instance n06NuStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := Prod.instModule

local instance n06NuStateParameterModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S × ℝ) := Prod.instModule

local instance n06NuHeightPairSMul (S : PhysicalSpacesData) :
    SMul ℝ (HeightPair S) := (n06NuHeightPairModule S).toSMul

local instance n06NuStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := (n06NuStateModule S).toSMul

local instance n06NuStateParameterSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) := (n06NuStateParameterModule S).toSMul

local instance n06NuHeightPairHSMul (S : PhysicalSpacesData) :
    HSMul ℝ (HeightPair S) (HeightPair S) :=
  ⟨@SMul.smul ℝ (HeightPair S) (n06NuHeightPairSMul S)⟩

local instance n06NuStateHSMul (S : PhysicalSpacesData) :
    HSMul ℝ (AnnularState S) (AnnularState S) :=
  ⟨@SMul.smul ℝ (AnnularState S) (n06NuStateSMul S)⟩

local instance n06NuStateParameterHSMul (S : PhysicalSpacesData) :
    HSMul ℝ (AnnularState S × ℝ) (AnnularState S × ℝ) :=
  ⟨@SMul.smul ℝ (AnnularState S × ℝ) (n06NuStateParameterSMul S)⟩

private theorem n06_convex_seminorm_pair
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x₀ : E) (ε : ℝ) :
    Convex ℝ {z : E × ℝ | p (z.1 - x₀) < ε ∧ |z.2| < ε} := by
  have heq : {z : E × ℝ | p (z.1 - x₀) < ε ∧ |z.2| < ε} =
      p.ball x₀ ε ×ˢ Metric.ball (0 : ℝ) ε := by
    ext z
    simp only [mem_setOf_eq, mem_prod, Seminorm.mem_ball,
      Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [heq]
  exact (p.convex_ball x₀ ε).prod (convex_ball (0 : ℝ) ε)

theorem n06_convex_stateNeighborhood (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) :
    Convex ℝ (stateNeighborhood S C base ε) :=
  n06_convex_seminorm_pair (stateGrading S base) C.referenceState ε

theorem n06_reference_state_segment_mem
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (C.referenceState, (0 : ℝ)) +
      (t • (z - (C.referenceState, 0)) : AnnularState S × ℝ) ∈
      stateNeighborhood S C base ε := by
  have href : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
    exact n05_referenceState_mem hN01.2.1
  have hmem : (C.referenceState, (0 : ℝ)) +
      (t • (z - (C.referenceState, 0)) : AnnularState S × ℝ) ∈
      segment ℝ (C.referenceState, (0 : ℝ)) z := by
    rw [segment_eq_image']
    exact ⟨t, ht, rfl⟩
  exact (n06_convex_stateNeighborhood S C base ε).segment_subset href hz hmem

theorem n06_reference_state_segment_sector
    (href : referenceStateConditions D S C)
    {z : AnnularState S × ℝ} (hs : stateSector S z.1) (t : ℝ) :
    stateSector S (((C.referenceState, (0 : ℝ)) +
      (t • (z - (C.referenceState, 0)) : AnnularState S × ℝ)).1) := by
  have h₀ : C.referenceState ∈ stateSectorSubmodule S := n05_referenceState_sector href
  have hz : z.1 ∈ stateSectorSubmodule S := hs
  exact (stateSectorSubmodule S).add_mem h₀
    ((stateSectorSubmodule S).smul_mem t ((stateSectorSubmodule S).sub_mem hz h₀))

theorem n06_stateU_mixedDerivative_affine
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x y : AnnularState S) (t : ℝ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (stateU S (x + (t • (y - x) : AnnularState S))) p =
      mixedDerivative a b (stateU S x) p +
        t * (mixedDerivative a b (stateU S y) p - mixedDerivative a b (stateU S x) p) := by
  have hfield : stateU S (x + (t • (y - x) : AnnularState S)) =
      (fun q => stateU S x q + t * (stateU S y q - stateU S x q)) := by
    change heightPairFieldLinear S (x.1 + t • (y.1 - x.1)) = _
    rw [map_add, map_smul, map_sub]
    rfl
  have hx := neighborhood_stateU_contDiff hT hS x
  have hy := neighborhood_stateU_contDiff hT hS y
  rw [hfield, spaces_mixedDerivative_add hx (contDiff_const.mul (hy.sub hx)),
    spaces_mixedDerivative_const_mul, n06_mixedDerivative_sub hy hx]

private theorem n06_scaled_affine {u v w t : ℝ} (c : ℝ)
    (h : w = u + t * (v - u)) :
    c * w = c * u + t * (c * v - c * u) := by
  rw [h]
  ring

private theorem n06_sub_affine {u v w u' v' w' t : ℝ}
    (h : w = u + t * (v - u)) (h' : w' = u' + t * (v' - u')) :
    w - w' = (u - u') + t * ((v - v') - (u - u')) := by
  rw [h, h']
  ring

private theorem n06_coordinate_array_affine (f : Fin 5 → ℝ)
    (u v w : Fin 7 → ℝ) (t : ℝ)
    (h : ∀ i, w i = u i + t * (v i - u i)) :
    (![f 0, f 1, f 2, f 3, f 4, w 0, w 1, w 2, w 3, w 4, w 5, w 6] :
        N06NuJetCoordinates) =
      ![f 0, f 1, f 2, f 3, f 4, u 0, u 1, u 2, u 3, u 4, u 5, u 6] +
        t • (![f 0, f 1, f 2, f 3, f 4, v 0, v 1, v 2, v 3, v 4, v 5, v 6] -
          ![f 0, f 1, f 2, f 3, f 4, u 0, u 1, u 2, u 3, u 4, u 5, u 6]) := by
  ext i
  fin_cases i <;>
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals first
  | exact h 0
  | exact h 1
  | exact h 2
  | exact h 3
  | exact h 4
  | exact h 5
  | exact h 6
  | ring

private def n06NuAffinePacket (S : PhysicalSpacesData)
    (y : AnnularState S × ℝ) (p : PolarPoint) : Fin 7 → ℝ :=
  ![mixedDerivative 1 0 (stateU S y.1) p,
    mixedDerivative 2 0 (stateU S y.1) p,
    (1 / p.1) * mixedDerivative 0 1 (stateU S y.1) p,
    (1 / p.1) * mixedDerivative 1 1 (stateU S y.1) p -
      (1 / p.1 ^ 2) * mixedDerivative 0 1 (stateU S y.1) p,
    (1 / p.1) * mixedDerivative 0 2 (stateU S y.1) p, y.2, y.1.2.1]

/-- All finite nu coordinates are affine along the very same original
state line. This is a literal equality of finite coordinate vectors. -/
theorem n06_actualNuJetCoordinates_affine
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (z w : AnnularState S × ℝ) (t : ℝ) {p : PolarPoint} (hr : p.1 ≠ 0) :
    n06ActualNuJetCoordinates D S (w + (t • (z - w) : AnnularState S × ℝ)) p =
      n06ActualNuJetCoordinates D S w p +
        t • (n06ActualNuJetCoordinates D S z p - n06ActualNuJetCoordinates D S w p) := by
  have hactual (y : AnnularState S × ℝ) : n06ActualNuJetCoordinates D S y p =
      n06NuCoordinateAngularJet D S y p.1 p.2 0 := by
    simpa only [iteratedDeriv_zero, Prod.eta] using
      n06_actualNuJetCoordinates_angularJet_eq hT hS y hr 0 p.2
  let s : AnnularState S × ℝ := w + (t • (z - w) : AnnularState S × ℝ)
  have hjet (a b : ℕ) :
      mixedDerivative a b (stateU S s.1) p = mixedDerivative a b (stateU S w.1) p +
        t * (mixedDerivative a b (stateU S z.1) p - mixedDerivative a b (stateU S w.1) p) :=
    n06_stateU_mixedDerivative_affine hT hS w.1 z.1 t a b p
  have h₀ := hjet 1 0
  have h₁ := hjet 2 0
  have h₂ := n06_scaled_affine (1 / p.1) (hjet 0 1)
  have h₃ := n06_sub_affine
    (n06_scaled_affine (1 / p.1) (hjet 1 1))
    (n06_scaled_affine (1 / p.1 ^ 2) (hjet 0 1))
  have h₄ := n06_scaled_affine (1 / p.1) (hjet 0 2)
  have hpacket : ∀ i : Fin 7, n06NuAffinePacket S s p i =
      n06NuAffinePacket S w p i + t * (n06NuAffinePacket S z p i - n06NuAffinePacket S w p i) := by
    intro i
    fin_cases i <;> first | exact h₀ | exact h₁ | exact h₂ | exact h₃ | exact h₄ | rfl
  have hj : n06NuCoordinateAngularJet D S s p.1 p.2 0 =
      n06NuCoordinateAngularJet D S w p.1 p.2 0 +
        t • (n06NuCoordinateAngularJet D S z p.1 p.2 0 -
          n06NuCoordinateAngularJet D S w p.1 p.2 0) :=
    n06_coordinate_array_affine ![p.1, D.w p.1, deriv D.w p.1, D.chi p.1, deriv D.chi p.1]
      (n06NuAffinePacket S w p) (n06NuAffinePacket S z p) (n06NuAffinePacket S s p) t hpacket
  exact (hactual s).trans (hj.trans (congrArg₂
    (fun a b : N06NuJetCoordinates => a + t • (b - a)) (hactual w).symm (hactual z).symm))

/-- The finite segment is contained in the genuine positive-discriminant
region on the support of the actual nu column. -/
theorem n06_actualNuJetDiscriminant_segment_lower
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hborder : p.1 ∈ tsupport D.chi) :
    ∀ v ∈ segment ℝ (n06ActualNuJetCoordinates D S (C.referenceState, 0) p)
      (n06ActualNuJetCoordinates D S z p), (1 / 2 : ℝ) ≤ n06NuFiniteDiscriminant v := by
  intro v hv
  rw [segment_eq_image'] at hv
  obtain ⟨t, ht, rfl⟩ := hv
  have hr : p.1 ≠ 0 := (hN01.1.1.choose_spec.1.1.trans hp.1.1).ne'
  have he := n06_actualNuJetCoordinates_affine hT hS z (C.referenceState, 0) t hr
  change (1 / 2 : ℝ) ≤ n06NuFiniteDiscriminant
    (n06ActualNuJetCoordinates D S (C.referenceState, 0) p +
      t • (n06ActualNuJetCoordinates D S z p -
        n06ActualNuJetCoordinates D S (C.referenceState, 0) p))
  rw [← he]
  exact n06_actualNuJetDiscriminant_lower hT hS hN01
    (n06_reference_state_segment_mem hN01 hz ht)
    (n06_reference_state_segment_sector hN01.2.2.1 hs t) hp hborder

end ContinuousFlexibility.Statements
