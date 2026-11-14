module

public import ContinuousFlexibility.Analysis.N01cHeightGeometry
public import ContinuousFlexibility.Analysis.N01cFullNeighborhood

/-!
# Normalized formulas for the actual nonlinear coefficients

The normalized curvature denominator Q/w lies in the fixed interval
[7/8, 9/8] on the original neighbourhood. The determinant identity removes
the apparent second radial height derivative from the corrected angular
coefficient and expresses it using this normalized denominator. The
remaining square-root denominator is controlled by the original D bounds.
These are identities for the original coefficients.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

private theorem sq_mul_inverseDThreeHalves {d : ℝ} (hd : 0 < d) :
    d ^ 2 * inverseDThreeHalves d = Real.sqrt d := by
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  unfold inverseDThreeHalves
  rw [mul_one_div]
  apply (div_eq_iff (mul_ne_zero hd.ne' hs)).mpr
  calc
    d ^ 2 = d * (Real.sqrt d) ^ 2 := by rw [Real.sq_sqrt hd.le]; ring
    _ = Real.sqrt d * (d * Real.sqrt d) := by ring

/-- A scalar consequence of the actual corrected determinant identity.
The denominator is Q/w, which is uniformly separated from zero in N01b. -/
theorem correctedCoefficient_normalized_of_determinant
    {w wr r d Q E pr c : ℝ}
    (hw : w ≠ 0) (hr : r ≠ 0) (hd : 0 < d) (hQ : Q ≠ 0)
    (hdet : (Q * inverseDThreeHalves d) * c -
        (-E * pr * inverseDThreeHalves d) ^ 2 = (w * wr / r) / d ^ 2) :
    c = (E ^ 2 * (pr / w) * pr * inverseDThreeHalves d +
      (wr / r) / Real.sqrt d) / (Q / w) := by
  let t := inverseDThreeHalves d
  have ht : t ≠ 0 := (inverseDThreeHalves_pos d hd).ne'
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hdt : d ^ 2 * t = Real.sqrt d := sq_mul_inverseDThreeHalves hd
  have hc : c = ((-E * pr * t) ^ 2 + (w * wr / r) / d ^ 2) / (Q * t) := by
    apply (eq_div_iff (mul_ne_zero hQ ht)).mpr
    change (Q * t) * c - (-E * pr * t) ^ 2 = (w * wr / r) / d ^ 2 at hdet
    nlinarith only [hdet]
  calc
    c = (-E * pr * t) ^ 2 / (Q * t) +
        ((w * wr / r) / d ^ 2) / (Q * t) := by rw [hc, add_div]
    _ = E ^ 2 * pr ^ 2 * t / Q + (w * wr / r) / (Q * (d ^ 2 * t)) := by
      field_simp [hr, hQ, ht, hd.ne'] <;> ring
    _ = E ^ 2 * pr ^ 2 * t / Q + (w * wr / r) / (Q * Real.sqrt d) := by rw [hdt]
    _ = (E ^ 2 * (pr / w) * pr * t + (wr / r) / Real.sqrt d) / (Q / w) := by
      field_simp [hw, hr, hQ, hs] <;> ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

/-- The exact normalized curvature denominator, using the FTC identities
for the original state height. -/
theorem n01_heightQ_div_profile
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) /
        stateProfile D S C z.1 p.1 =
      1 + z.2 * ((heightRadial (stateU S z.1) p +
        profileEnergy (stateProfile D S C z.1) p *
          angularPartial (heightAngular (stateU S z.1)) p) /
            stateProfile D S C z.1 p.1) := by
  obtain ⟨_, hRef⟩ := hA.1.1
  have hr : p.1 ≠ 0 := (hRef.1.1.trans hp.1.1).ne'
  have hw := (n01PartB_denominators_pos hRef.1 hS hA.2.1 hB hz hp).1.ne'
  rw [heightQ, heightRadial_stateHeight hS hT hA,
    angularPartial_heightAngular_stateHeight hS hT hA z hr]
  field_simp [hw] <;> ring

/-- The discriminant differs from one only through the actual height
direction and the real perturbation parameter. -/
theorem n01_polarDiscriminant_stateHeight
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (z : AnnularState S × ℝ) (p : PolarPoint) :
    polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p =
      1 - 2 * stateProfile D S C z.1 p.1 * z.2 * heightRadial (stateU S z.1) p -
        z.2 ^ 2 * ((heightRadial (stateU S z.1) p) ^ 2 +
          profileEnergy (stateProfile D S C z.1) p * (heightAngular (stateU S z.1) p) ^ 2) := by
  rw [polarDiscriminant, heightRadial_stateHeight hS hT hA,
    heightAngular_stateHeight hS hT hA]
  unfold heightDiscriminant profileEnergy radialEnergy
  ring

/-- The corrected angular coefficient expressed with the normalized Q/w
denominator and the actual mixed height jet. This identity is valid on
the full N01b neighbourhood. -/
theorem n01_originalCoefficientC_normalized
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    let w := stateProfile D S C z.1
    let h := stateHeight D S C z
    let E := profileEnergy w p
    let Q := heightQ E (heightRadial h p) (angularPartial (heightAngular h) p)
    let pr := radialPartial (heightAngular h) p
    let d := polarDiscriminant w h p
    (originalCoefficients D S C z).c p =
      (E ^ 2 * (pr / w p.1) * pr * inverseDThreeHalves d +
        (deriv w p.1 / p.1) / Real.sqrt d) / (Q / w p.1) := by
  obtain ⟨_, hRef⟩ := hA.1.1
  have hr : p.1 ≠ 0 := (hRef.1.1.trans hp.1.1).ne'
  have hd := n01PartB_denominators_pos hRef.1 hS hA.2.1 hB hz hp
  have hw : DifferentiableAt ℝ (stateProfile D S C z.1) p.1 :=
    (contDiff_stateProfile_of_partA hS hT hA z.1).differentiable (by simp) p.1
  have hdet := polar_corrected_determinant (stateHeight D S C z) hw hr hd.2.2 hd.2.1.ne'
  exact correctedCoefficient_normalized_of_determinant hd.1.ne' hr hd.2.2 hd.2.1.ne' hdet

end ContinuousFlexibility.Statements
