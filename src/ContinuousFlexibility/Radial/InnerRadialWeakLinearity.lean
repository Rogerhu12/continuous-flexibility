module

public import ContinuousFlexibility.Radial.InnerRadialFiniteWeakGraph

/-! # Linearity and continuity of the actual physical weak residual -/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements
open scoped InnerProductSpace

theorem innerRadialWeakResidual_continuous (D : ReferenceData)
    (q : InnerRadialH1Pair D) (v f g : RadialModeL2 D) (scalar : ℝ) :
    Continuous (innerRadialWeakResidual D q v f g scalar) := by
  change Continuous (fun T : InnerRadialH1Pair D =>
    ⟪q.2, T.2⟫_ℝ + ⟪v, T.1⟫_ℝ + scalar * ⟪g, T.1⟫_ℝ - ⟪f, T.1⟫_ℝ)
  exact (((continuous_const.inner continuous_snd).add
    (continuous_const.inner continuous_fst)).add
    (continuous_const.mul (continuous_const.inner continuous_fst))).sub
    (continuous_const.inner continuous_fst)

theorem innerRadialWeakResidual_add_solution (D : ReferenceData)
    (q q' : InnerRadialH1Pair D) (v v' f f' g : RadialModeL2 D)
    (scalar scalar' : ℝ) (T : InnerRadialH1Pair D) :
    innerRadialWeakResidual D (q + q') (v + v') (f + f') g (scalar + scalar') T =
      innerRadialWeakResidual D q v f g scalar T +
        innerRadialWeakResidual D q' v' f' g scalar' T := by
  simp only [innerRadialWeakResidual_apply, Prod.snd_add, inner_add_left]
  ring

theorem innerRadialWeakResidual_smul_solution (D : ReferenceData)
    (c : ℝ) (q : InnerRadialH1Pair D) (v f g : RadialModeL2 D)
    (scalar : ℝ) (T : InnerRadialH1Pair D) :
    innerRadialWeakResidual D (c • q) (c • v) (c • f) g (c * scalar) T =
      c * innerRadialWeakResidual D q v f g scalar T := by
  simp only [innerRadialWeakResidual_apply, Prod.smul_snd, real_inner_smul_left]
  ring

end ContinuousFlexibility.Radial
