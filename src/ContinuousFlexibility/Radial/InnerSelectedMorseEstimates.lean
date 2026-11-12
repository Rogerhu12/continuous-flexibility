import ContinuousFlexibility.Radial.InnerSelectedPhysicalModels
import ContinuousFlexibility.Radial.InnerMorseScaledPhysicalPoisson

/-!
# Estimates for the same actual selected tail models

The selected-model remainder and full conormal error are transported
through the exact independently scaled chart. The column estimate is
stated for weights on the actual physical closed interval, so the
canonical finite-chain interpolation supplies it directly.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

namespace InnerSelectedPhysicalGeometry

variable {S : SelectedTailData} {D : ReferenceData} {X₀ : ℝ}
  (P : InnerSelectedPhysicalGeometry S D X₀)
  {a CM KM η : ℝ}
  (hfamily : InnerMorsePhysicalFamily a S.Cstar S.chain.index CM KM η)
  (hsupport : innerCentralModelBorderRadius < X₀)
  (K q : ℕ) (hq : 1 ≤ q)
  (hband : radialFrequencyBand S.chain S.Cstar (S.chain.index + K) (2 * q))
  (side : Bool) (p : Fin K)

/-- Both signs use the full error matrix of the same selected model,
with its true side-dependent physical height. -/
theorem tailModel_error_lt {γ : ℝ} (hγ : |γ| ≤ 1) (sign : Bool) :
    ‖innerTwoCutWeightedError
      (P.tailModel hfamily hsupport K q hq hband side p).kappa
      (innerMorseCutWeight S.chain.index a γ side
        (innerMorseInnerTailIndex S.chain.index K side p))
      (P.tailModel hfamily hsupport K q hq hband side p).errorMatrix sign‖ < η := by
  rw [P.tailModel_kappa hfamily hsupport K q hq hband side p,
    P.tailModel_errorMatrix hfamily hsupport K q hq hband side p]
  exact innerSelectedMorseModel_error hfamily P.realization rfl
    (innerMorseInnerTailIndex S.chain.index K side p) (S.chain.index + K) q
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).2 hq hband hγ side
    (mul_pos (P.heightScale_pos side)
      (innerMorseChain_height_pos P.realization side
        (innerMorseInnerTailIndex_bounds S.chain.index K side p).1)) sign

theorem tailModel_error_le {γ : ℝ} (hγ : |γ| ≤ 1) (sign : Bool) :
    ‖innerTwoCutWeightedError
      (P.tailModel hfamily hsupport K q hq hband side p).kappa
      (innerMorseCutWeight S.chain.index a γ side
        (innerMorseInnerTailIndex S.chain.index K side p))
      (P.tailModel hfamily hsupport K q hq hband side p).errorMatrix sign‖ ≤ η :=
  (P.tailModel_error_lt hfamily hsupport K q hq hband side p hγ sign).le

/-- The fixed exponent thirty-six applies to the very Dirichlet map
stored in the actual physical model dictionary. -/
theorem tailModel_dirichlet_norm_le (hCM : 0 ≤ CM) :
    ‖(P.tailModel hfamily hsupport K q hq hband side p).dirichlet‖ ≤
      innerMorseDirichletConstant CM *
        radialE (innerMorseInnerTailIndex S.chain.index K side p) ^ (36 : ℝ) := by
  have hj : 1 ≤ (2 : ℝ) * q := by exact_mod_cast (show 1 ≤ 2 * q by omega)
  exact innerMorseScaledPhysicalModelChart_dirichlet_cost P.realization P.index_ge D (P.chain K)
    (decide (q = 1)) ((2 : ℝ) * q)
    (innerModelChainPiece (innerMorseInnerCenter K))
    (innerModelChainPiece (innerMorseInnerTailSlot K side p))
    (P.centralColumn q hsupport) side
    (innerMorseInnerTailIndex S.chain.index K side p)
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    (P.radiusScale side) (P.heightScale side)
    (P.radiusScale_pos side) (P.heightScale_pos side)
    (fun _ hx => P.tail_profile side
      (innerMorseInnerTailIndex_bounds S.chain.index K side p).1 hx)
    (innerMorseInnerTailPiece_ne_center K side p)
    (P.tail_left K side p) (P.tail_right K side p)
    (P.tailModel_hypotheses hfamily K q hq hband side p)
    (P.tailLocalizedModel hfamily K q hq hband side p) hj hCM

/-- The actual physical weight need only have the canonical
interpolation on this closed piece. The cap and remainder estimates
are derived from the same selected model and original radius ODE. -/
theorem tailModel_column_norm_le
    (ha : 0 ≤ a) (hN : 4096 ≤ S.chain.index) (hNa : 64 * a ≤ (S.chain.index : ℝ))
    (hCM : 0 < CM) (γ sign : ℝ) (hγ : |γ| ≤ 1) (hsign : |sign| ≤ 1)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (hinterp :
      let A := P.tailModel hfamily hsupport K q hq hband side p
      ∀ r ∈ Icc ((P.chain K).left (innerModelChainPiece (innerMorseInnerTailSlot K side p)))
          ((P.chain K).right (innerModelChainPiece (innerMorseInnerTailSlot K side p))),
        W r = (innerMorseInterpolatedWeight S.chain.index a γ side
          (innerMorseInnerTailIndex S.chain.index K side p) A.leftWall A.rightWall r) ^ sign)
    (i : Fin 2) :
    let A := P.tailModel hfamily hsupport K q hq hband side p
    ‖((innerMorseCutWeight S.chain.index a γ side
          (innerMorseInnerTailIndex S.chain.index K side p) i) ^ sign *
        sqrt (A.kappa i))⁻¹ •
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) (A.column i)‖ ≤
          innerMorsePoissonConstant / ((2 : ℝ) * q) := by
  let A := P.tailModel hfamily hsupport K q hq hband side p
  have hmono : MonotoneOn A.radius (Icc A.buffer.l A.buffer.h) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) A.radius_smooth.continuous.continuousOn
      (fun x hx => (A.chart_pos x (interior_subset hx)).2.1)).monotoneOn
  have hmap {x : ℝ} (hx : x ∈ Icc A.buffer.l A.buffer.h) :
      A.radius x ∈
        Icc ((P.chain K).left (innerModelChainPiece (innerMorseInnerTailSlot K side p)))
          ((P.chain K).right (innerModelChainPiece (innerMorseInnerTailSlot K side p))) := by
    rw [A.left_eq, A.right_eq]
    exact ⟨hmono (left_mem_Icc.mpr A.buffer_hypotheses.1.le) hx hx.1,
      hmono hx (right_mem_Icc.mpr A.buffer_hypotheses.1.le) hx.2⟩
  have hbuffer (x : ℝ) (hx : x ∈ Icc A.buffer.l A.buffer.h) :
      W (A.radius x) =
        (innerMorseInterpolatedWeight S.chain.index a γ side
          (innerMorseInnerTailIndex S.chain.index K side p)
          A.leftWall A.rightWall (A.radius x)) ^ sign :=
    hinterp (A.radius x) (hmap hx)
  have hj : 1 ≤ (2 : ℝ) * q := by exact_mod_cast (show 1 ≤ 2 * q by omega)
  exact innerMorseScaledPhysicalModelChart_poisson_bound P.realization P.index_ge D (P.chain K)
    (decide (q = 1)) ((2 : ℝ) * q)
    (innerModelChainPiece (innerMorseInnerCenter K))
    (innerModelChainPiece (innerMorseInnerTailSlot K side p))
    (P.centralColumn q hsupport) side
    (innerMorseInnerTailIndex S.chain.index K side p)
    (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    (P.radiusScale side) (P.heightScale side)
    (P.radiusScale_pos side) (P.heightScale_pos side)
    (fun _ hx => P.tail_profile side
      (innerMorseInnerTailIndex_bounds S.chain.index K side p).1 hx)
    (innerMorseInnerTailPiece_ne_center K side p)
    (P.tail_left K side p) (P.tail_right K side p)
    (P.tailModel_hypotheses hfamily K q hq hband side p)
    (P.tailLocalizedModel hfamily K q hq hband side p)
    S.chain.index ha hN hNa (innerMorseInnerTailIndex_bounds S.chain.index K side p).1
    hj hCM (P.tailLocalizedModel_remainder hfamily K q hq hband side p)
    γ sign hγ hsign W hW CW hWC hbuffer i

end InnerSelectedPhysicalGeometry

end ContinuousFlexibility.Radial
