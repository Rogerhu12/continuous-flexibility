import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData

/-!
# Every actual atom on a retained negative half

The whole atlas copies the same negative chart, inverse, height, principal
field, potential, endpoints and sample. Therefore all thirty-three atom
functions are copied, at every state and every point. This identity also
applies after enlarging only the material envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements CanonicalGeometry

/-- Transfer actual atom functions along the negative branch of the whole
reference atlas. The selected old half is required to be negative so the
three divided atoms are the same literal zero functions. No regularity,
numerical estimate or identification of distinct host cells is assumed. -/
theorem n04WholeReferenceGaugeAtlasData_negative_atom
    {D : ReferenceData} (T : MaterialData) {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (e : ℕ ≃ N04WholePieceIndex D)
    (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
    (ψ χ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
    (τ σ : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
    (Q : (AnnularState S × ℝ) →
      N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ) (N : Set ℝ)
    (z : AnnularState S × ℝ) (m : ℕ) (j : ℕ × Bool) (hi : e m = .inl j)
    (hnegative : K.positive (if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1) = false)
    (v : Atom) :
    let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
    let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
    atom D T S C L V z m v = atom D T S C L K z k v := by
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ h₀ τ σ Q N
  let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
  change atom D T S C L V z m v = atom D T S C L K z k v
  rcases n04WholeReferenceGaugeAtlasData_negative_fields
    C L K e cell ψ χ h₀ τ σ Q N z m j hi with
    ⟨hl, hr, hpl, hpr, _, hcell, hneg, hF, hG, hH, hcoeff, hpotential⟩
  have hphysical : physicalUnitPoint V m = physicalUnitPoint K k := by
    funext p
    simp only [physicalUnitPoint, hpl, hpr]
  have hcanonical : canonicalUnitPoint V m = canonicalUnitPoint K k := by
    funext p
    simp only [canonicalUnitPoint, hl, hr]
  have hsource (f : PolarPoint → ℝ) :
      canonicalSource S V z m f = canonicalSource S K z k f := by
    funext p
    simp only [canonicalSource, hF, hG, hH]
  cases v <;> funext p <;>
    simp only [atom, hphysical, hcanonical, hl, hr, hpl, hpr, hcell,
      hneg, hnegative, hF, hG, hH, hcoeff, hpotential, hsource,
      Bool.false_eq_true, ite_false]

end ContinuousFlexibility.Analysis
