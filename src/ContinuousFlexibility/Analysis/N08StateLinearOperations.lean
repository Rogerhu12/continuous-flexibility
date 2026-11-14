module

public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Scalar multiplication through the specified real module

The state is a nested product of projective physical spaces. These wrappers
use the already specified module structure directly, so writing an affine
state line does not start a separate search for a scalar action.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

def n08RealSMul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (t : ℝ) (x : E) : E := t • x

def n08StateSMul (S : PhysicalSpacesData) (t : ℝ) (x : AnnularState S) : AnnularState S :=
  n08RealSMul (E := AnnularState S) t x

def n08StateParameterSMul (S : PhysicalSpacesData) (t : ℝ)
    (x : AnnularState S × ℝ) : AnnularState S × ℝ :=
  n08RealSMul (E := AnnularState S × ℝ) t x

end ContinuousFlexibility.Statements
