module

public import ContinuousFlexibility.Analysis.N06PrimitiveFiniteCoreGreenData
public import ContinuousFlexibility.Analysis.N06OperatorExtension

/-!
# The actual relative source satisfies the original physical relation

The principal compact-test pairing, its genuine zero value on negative
pieces, and the literal full source identity determine every finite-core
Green formula. The primitive transmission identities cancel its actual
interfaces. Density and closed physical tests then pass the equation to
every vector of the original graph, with its original normalization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis CanonicalGeometry

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b} {z : AnnularState S × ℝ}

local instance n06PrimitivePhysicalLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n06PrimitivePhysicalLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _
local instance n06PrimitivePhysicalGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06PrimitivePhysicalGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

/-- The actual source package gives the original perturbed relation for
the same K, V and B. The three source inputs are precisely the conclusions
of the primitive principal and scalar source construction; no global weak
equation, finite Green record, or endpoint matching is assumed. -/
theorem n06_primitiveRelative_operator_physical
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hradial : ReferenceRadial S C K) (hAux : AuxiliaryColumnGauge S K)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (htransmission : TransmissionGeometry D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (Mc M : V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (hweak : ∀ F : V.level (3 / 4 : ℝ) 0 b, ∀ m, K.positive m = true →
      ∀ φ, CanonicalTest S K m φ →
        (∫ p, V.forget (3 / 4 : ℝ) 0 b (Mc F) m p * φ p ∂canonicalMeasure S K m) =
          ∫ p, (B.inverse F).val.1.1 m p * divergenceOperator
            (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
              (K.dividedDifference z m).a (K.dividedDifference z m).b
              (K.dividedDifference z m).c) φ p ∂canonicalMeasure S K m)
    (hnegative : ∀ F : V.level (3 / 4 : ℝ) 0 b, ∀ m,
      K.positive m ≠ true → V.forget (3 / 4 : ℝ) 0 b (Mc F) m = 0)
    (hsource : ∀ F : V.level (3 / 4 : ℝ) 0 b, ∀ m,
      (V.forget (3 / 4 : ℝ) 0 b (F + M F) m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          n06CurrentRelativeSourceField D S C L K z (B.inverse F).val.1
            (V.forget (3 / 4 : ℝ) 0 b F)
            (V.forget (3 / 4 : ℝ) 0 b (Mc F)) m) :
    ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b (n06OperatorFromRelative B M u)) := by
  apply n06_perturbedCanonicalRelation_of_primitiveFiniteGreenCore
    hT hS h hradial hAux href hcur hz hs (n06OperatorFromRelative B M)
  intro u hu
  have hinverse : B.inverse u.val.2 = u := h.2.2.2.2.2.2.2.2.2.1 u
  have hsourceU : ∀ m,
      (V.forget (3 / 4 : ℝ) 0 b (n06OperatorFromRelative B M u) m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          n06CurrentRelativeSourceField D S C L K z u.val.1
            (V.forget (3 / 4 : ℝ) 0 b u.val.2)
            (V.forget (3 / 4 : ℝ) 0 b (Mc u.val.2)) m := by
    intro m
    simpa only [n06OperatorFromRelative_apply, hinverse] using hsource u.val.2 m
  have hweakU : ∀ m, K.positive m = true → ∀ φ, CanonicalTest S K m φ →
      (∫ p, V.forget (3 / 4 : ℝ) 0 b (Mc u.val.2) m p * φ p ∂canonicalMeasure S K m) =
        ∫ p, u.val.1.1 m p * divergenceOperator
          (n06CubicCoefficients (fun q => (q.1 - K.left m) * (K.right m - q.1))
            (K.dividedDifference z m).a (K.dividedDifference z m).b
            (K.dividedDifference z m).c) φ p ∂canonicalMeasure S K m := by
    intro m hm φ hφ
    simpa only [hinverse] using hweak u.val.2 m hm φ hφ
  exact n06N05_primitive_finiteCore_greenData hT hS h hradial href hcur hprincipal
    htransmission hz hs u hu (V.forget (3 / 4 : ℝ) 0 b (Mc u.val.2))
    (V.forget (3 / 4 : ℝ) 0 b (n06OperatorFromRelative B M u))
    hsourceU hweakU (hnegative u.val.2)

end ContinuousFlexibility.Statements
