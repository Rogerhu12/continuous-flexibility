module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.TameInverseFamily

/-!+# The actual Banach solution used in the regularity bootstrap

The first inverse acts on the single source level supplied by N06.  Composing
it with the reference graph inverse gives a solution of the perturbed weak
equation.  All identities below concern those two existing inverses; no new
solution or regularity assumption is introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {L : ReturnCorrectionData S} {V : VolumeModelData S K} {b : ℕ}
  (B : CanonicalDomainData S K V b) (P : RelativeInverseData S K V b B)

-- Cache the inherited structures on the nested graph subtypes.  In
-- particular, operator norms need not search again through both lp layers.
local instance : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _

local instance : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _

local instance : NormedAddCommGroup (CanonicalUnknown S K) := inferInstance

local instance : NormedSpace ℝ (CanonicalUnknown S K) := inferInstance

local instance : NormedAddCommGroup B.Space := Submodule.normedAddCommGroup _

local instance : NormedSpace ℝ B.Space := Submodule.normedSpace _

/-- The Banach solution is the reference graph inverse applied to the
relative inverse on the prescribed base source space. -/
def n07aBaseInverse (z : AnnularState S × ℝ) :
    V.level (3 / 4 : ℝ) 0 b →L[ℝ] B.Space :=
  B.inverse.comp (P.inverse z)

theorem n07aBaseInverse_apply (z : AnnularState S × ℝ)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    n07aBaseInverse B P z F = B.inverse (P.inverse z F) :=
  ContinuousLinearMap.comp_apply B.inverse (P.inverse z) F

variable {B P}

/-- Its reference source is exactly the relative inverse source. -/
theorem n07aBaseInverse_source
    (h05 : N05Properties D T S C K V b B) (z : AnnularState S × ℝ)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    (n07aBaseInverse B P z F).val.2 = P.inverse z F := by
  rw [n07aBaseInverse_apply]
  exact h05.2.2.2.2.2.2.2.1 _

/-- Its unknown is the very same global reference inverse used by N05's
weighted estimates. -/
theorem n07aBaseInverse_global
    (h05 : N05Properties D T S C K V b B) (z : AnnularState S × ℝ)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    (n07aBaseInverse B P z F).val.1 =
      B.globalInverse (V.forget (3 / 4 : ℝ) 0 b (P.inverse z F)) := by
  rw [n07aBaseInverse_apply]
  exact h05.2.2.2.2.2.2.2.2.2.1 _

variable {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The existing Neumann identities give the right inverse on the base
source space without a second inversion. -/
theorem n07aBaseInverse_rightInverse
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    P.operator z (n07aBaseInverse B P z F) = F := by
  have h := h06.2 z hz hs
  rw [h.2.2.2.1, n07aBaseInverse_source h05]
  exact (h.2.2.2.2.1 F).2

/-- The reference section identity and the same Neumann identities give
the left inverse on the whole fixed graph domain. -/
theorem n07aBaseInverse_leftInverse
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) :
    n07aBaseInverse B P z (P.operator z u) = u := by
  have h := h06.2 z hz hs
  rw [n07aBaseInverse_apply, h.2.2.2.1,
    (h.2.2.2.2.1 u.val.2).1]
  exact h05.2.2.2.2.2.2.2.2.1 u

/-- A fixed-graph solution is uniquely the Banach solution. -/
theorem n07aBaseInverse_eq_of_operator
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {u : B.Space} {F : V.level (3 / 4 : ℝ) 0 b}
    (hu : P.operator z u = F) :
    n07aBaseInverse B P z F = u := by
  rw [← hu]
  exact n07aBaseInverse_leftInverse h05 h06 hz hs u

theorem n07a_operator_injective
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) :
    Function.Injective (P.operator z) := by
  exact (show Function.LeftInverse (n07aBaseInverse B P z) (P.operator z) from
    n07aBaseInverse_leftInverse h05 h06 hz hs).injective

theorem n07a_operator_surjective
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) :
    Function.Surjective (P.operator z) := by
  exact (show Function.RightInverse (n07aBaseInverse B P z) (P.operator z) from
    n07aBaseInverse_rightInverse h05 h06 hz hs).surjective

/-- This solution satisfies the actual weak physical equation and the
normalization row from the frozen N06 relation. -/
theorem n07aBaseInverse_perturbed
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    PerturbedCanonicalRelation D S C K L z (n07aBaseInverse B P z F).val.1
      (V.forget (3 / 4 : ℝ) 0 b F) := by
  have h := (h06.2 z hz hs).1 (n07aBaseInverse B P z F)
  rw [n07aBaseInverse_rightInverse h05 h06 hz hs] at h
  exact h

/-- The base bound uses the factor two already proved for the first
Neumann inverse. -/
theorem n07aBaseInverse_opNorm_le
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1) :
    ‖n07aBaseInverse B P z‖ ≤ 2 * ‖B.inverse‖ := by
  calc
    ‖n07aBaseInverse B P z‖ ≤ ‖B.inverse‖ * ‖P.inverse z‖ :=
      ContinuousLinearMap.opNorm_comp_le B.inverse (P.inverse z)
    _ ≤ ‖B.inverse‖ * 2 :=
      mul_le_mul_of_nonneg_left (h06.2 z hz hs).2.2.2.2.2 (norm_nonneg _)
    _ = 2 * ‖B.inverse‖ := mul_comm _ _

theorem n07aBaseInverse_bound
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    ‖n07aBaseInverse B P z F‖ ≤ (2 * ‖B.inverse‖) * ‖F‖ := by
  exact (ContinuousLinearMap.le_opNorm (n07aBaseInverse B P z) F).trans
    (mul_le_mul_of_nonneg_right (n07aBaseInverse_opNorm_le h06 hz hs) (norm_nonneg F))

/-- A resolvent identity in the actual fixed domain.  The later continuity
argument only has to control the change in the forward operator. -/
theorem n07aBaseInverse_resolvent
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {z' : AnnularState S × ℝ}
    (hz' : z' ∈ stateNeighborhood S C base ε) (hs' : stateSector S z'.1)
    (F F' : V.level (3 / 4 : ℝ) 0 b) :
    n07aBaseInverse B P z' F' - n07aBaseInverse B P z F =
      n07aBaseInverse B P z'
        ((F' - F) - (P.operator z' (n07aBaseInverse B P z F) -
          P.operator z (n07aBaseInverse B P z F))) := by
  exact inverseFamily_resolvent
    (fun x => (P.operator x).toLinearMap)
    (fun x => (n07aBaseInverse B P x).toLinearMap)
    (n07aBaseInverse_leftInverse h05 h06 hz' hs')
    (n07aBaseInverse_rightInverse h05 h06 hz hs) F F'

end ContinuousFlexibility.Analysis
