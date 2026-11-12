import ContinuousFlexibility.Radial.InnerRadialActualAssembly
import ContinuousFlexibility.Radial.InnerMorseInnerWeights

/-!
# Interpolation walls from the actual finite-chain dictionary

Each model uses its original physical inner walls. Each gap uses its
actual endpoints. These walls define the existing finite-chain weight
on the same physical geometry and recover the original interpolation
on every closed model chart.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

namespace InnerRadialModelChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central piece : Fin (n + 1)} {column : RadialModeL2 D}
  (M : InnerRadialModelChart D G bordered j central column piece)

theorem matchedRadius_strictMonoOn : StrictMonoOn M.radius (Icc M.buffer.l M.buffer.h) :=
  strictMonoOn_of_deriv_pos (convex_Icc _ _) M.radius_smooth.continuous.continuousOn
    (fun x hx => (M.chart_pos x (interior_subset hx)).2.1)

theorem matchedRadius_mem_Icc {x : ℝ} (hx : x ∈ Icc M.buffer.l M.buffer.h) :
    M.radius x ∈ Icc (G.left piece) (G.right piece) := by
  rw [M.left_eq, M.right_eq]
  exact ⟨M.matchedRadius_strictMonoOn.monotoneOn
      (left_mem_Icc.mpr M.buffer_hypotheses.1.le) hx hx.1,
    M.matchedRadius_strictMonoOn.monotoneOn hx
      (right_mem_Icc.mpr M.buffer_hypotheses.1.le) hx.2⟩

theorem matched_innerWalls_order :
    G.left piece < M.radius (bufferInnerWall M.buffer 0) ∧
      M.radius (bufferInnerWall M.buffer 0) < M.radius (bufferInnerWall M.buffer 1) ∧
      M.radius (bufferInnerWall M.buffer 1) < G.right piece := by
  obtain ⟨h0, h01, h1⟩ := innerBuffer_walls_inside M.buffer_hypotheses
  have hx0 : bufferInnerWall M.buffer 0 ∈ Icc M.buffer.l M.buffer.h :=
    ⟨h0.le, (h01.trans h1).le⟩
  have hx1 : bufferInnerWall M.buffer 1 ∈ Icc M.buffer.l M.buffer.h :=
    ⟨(h0.trans h01).le, h1.le⟩
  rw [M.left_eq, M.right_eq]
  exact ⟨M.matchedRadius_strictMonoOn (left_mem_Icc.mpr M.buffer_hypotheses.1.le) hx0 h0,
    M.matchedRadius_strictMonoOn hx0 hx1 h01,
    M.matchedRadius_strictMonoOn hx1 (right_mem_Icc.mpr M.buffer_hypotheses.1.le) h1⟩

end InnerRadialModelChart

namespace InnerRadialActualChain

section Walls

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

def matchedWeightLeft (p : Fin (n + 1)) : ℝ :=
  match C.piece p with
  | .inl M => M.radius (bufferInnerWall M.buffer 0)
  | .inr _ => G.left p

def matchedWeightRight (p : Fin (n + 1)) : ℝ :=
  match C.piece p with
  | .inl M => M.radius (bufferInnerWall M.buffer 1)
  | .inr _ => G.right p

theorem matchedWeightLeft_model {p : Fin (n + 1)}
    (M : InnerRadialModelChart D G bordered j central column p)
    (hp : C.piece p = .inl M) :
    C.matchedWeightLeft p = M.radius (bufferInnerWall M.buffer 0) := by
  simp only [matchedWeightLeft, hp]

theorem matchedWeightRight_model {p : Fin (n + 1)}
    (M : InnerRadialModelChart D G bordered j central column p)
    (hp : C.piece p = .inl M) :
    C.matchedWeightRight p = M.radius (bufferInnerWall M.buffer 1) := by
  simp only [matchedWeightRight, hp]

theorem matchedWeight_order (p : Fin (n + 1)) :
    G.left p ≤ C.matchedWeightLeft p ∧
      C.matchedWeightLeft p < C.matchedWeightRight p ∧
      C.matchedWeightRight p ≤ G.right p := by
  cases hp : C.piece p with
  | inl M =>
      have h := M.matched_innerWalls_order
      simpa only [matchedWeightLeft, matchedWeightRight, hp] using
        (show G.left p ≤ M.radius (bufferInnerWall M.buffer 0) ∧
          M.radius (bufferInnerWall M.buffer 0) < M.radius (bufferInnerWall M.buffer 1) ∧
          M.radius (bufferInnerWall M.buffer 1) ≤ G.right p from
          ⟨h.1.le, h.2.1, h.2.2.le⟩)
  | inr Q =>
      simpa only [matchedWeightLeft, matchedWeightRight, hp] using
        (show G.left p ≤ G.left p ∧ G.left p < G.right p ∧ G.right p ≤ G.right p from
          ⟨le_rfl, G.left_lt_right p, le_rfl⟩)

end Walls

section MorseWeight

variable {D : ReferenceData} (N K : ℕ) (a γ : ℝ)
  {G : InnerRadialChainGeometry D (2 * (2 * K + 1))}
  {bordered : Bool} {j : ℝ} {central : Fin (2 * (2 * K + 1) + 1)}
  {column : RadialModeL2 D}
  (C : InnerRadialActualChain D G bordered j central column)

/-- The already defined physical chain weight has the exact original
interpolation on each actual model, including both closed endpoints. -/
theorem matchedWeight_on_closed_model (p : Fin (2 * K + 1))
    (M : InnerRadialModelChart D G bordered j central column (innerModelChainPiece p))
    (hp : C.piece (innerModelChainPiece p) = .inl M)
    {x : ℝ} (hx : x ∈ Icc M.buffer.l M.buffer.h) :
    innerMorseInnerWeight N K a γ G C.matchedWeightLeft C.matchedWeightRight (M.radius x) =
      innerInterpolatedWeight (M.radius (bufferInnerWall M.buffer 0))
        (M.radius (bufferInnerWall M.buffer 1))
        (innerMorseInnerModelWeight N K a γ p 0) (innerMorseInnerModelWeight N K a γ p 1)
        (M.radius x) := by
  have h := innerMorseInnerWeight_on_closed_model N K a γ G
    C.matchedWeightLeft C.matchedWeightRight
    (fun q => (C.matchedWeight_order q).2.1)
    (fun q => (C.matchedWeight_order q).2.2) p
    (C.matchedWeight_order (innerModelChainPiece p)).1 (M.matchedRadius_mem_Icc hx)
  simpa only [C.matchedWeightLeft_model M hp, C.matchedWeightRight_model M hp] using h

end MorseWeight

end InnerRadialActualChain

end ContinuousFlexibility.Radial
