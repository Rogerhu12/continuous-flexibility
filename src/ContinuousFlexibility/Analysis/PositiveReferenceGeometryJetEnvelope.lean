import ContinuousFlexibility.Analysis.RadialReferencePotentialJetEnvelope
import ContinuousFlexibility.Analysis.PositiveChartRangeGeometry

/-!
# Finite jets of the displayed positive reference geometry

The physical unit coordinate and canonical unit coordinate remain
distinct. Their zeroth normalized values are bounded using the genuine
range certificate. Positive jets, reciprocal height, and interval costs
come from the same finite material envelope. The source factors use the
actual positive derivative of the inverse coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff

def positiveReferenceGeometryScalar (l r : ℝ) (Y H : ℝ → ℝ) : Atom → ℝ → ℝ
  | .chartRadial => fun t => Y (l + (r - l) * t)
  | .inverseRadial => fun t => (Function.invFun Y t - l) / (r - l)
  | .height => fun t => H (l + (r - l) * t)
  | .heightInverse => fun t => (H (l + (r - l) * t))⁻¹
  | .jacobian => fun t => deriv Y (l + (r - l) * t)
  | .jacobianInverse => fun t => deriv (Function.invFun Y) (Y (l + (r - l) * t))
  | .sourceFactor => fun t => H (Function.invFun Y t) * deriv (Function.invFun Y) t
  | .sourceFactorInverse => fun t =>
      (H (Function.invFun Y t))⁻¹ * deriv Y (Function.invFun Y t)
  | _ => fun _ => 0

private theorem positiveReferenceGeometry_affine_jets
    {M : ℝ} (hM : 0 ≤ M) (a b x : ℝ) (hb : |b| ≤ M)
    (k : ℕ) (hk : 1 ≤ k) :
    |iteratedDeriv k (fun t : ℝ => a + b * t) x| ≤ M := by
  rw [iteratedDeriv_const_add (by omega : 0 < k) a,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_id, if_neg (by omega : k ≠ 0)]
  by_cases h1 : k = 1
  · simpa only [if_pos h1, mul_one] using hb
  · simpa only [if_neg h1, mul_zero, abs_zero] using hM

/-- The same finite envelope controls all geometric scalar formulas.
The coefficient precedes every interval, field and numerical input. -/
theorem exists_positiveReferenceGeometry_jet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M : ℝ}, 1 ≤ M →
      ∀ {l r : ℝ}, l < r → r - l ≤ M → (r - l)⁻¹ ≤ M →
      ∀ Y H : ℝ → ℝ,
      PositiveChartRangeGeometry (positiveReferenceCylinderChart Y)
        (positiveReferenceCylinderInverse Y) (fun p : PolarPoint => H p.1) l r 0 1 →
      (∀ k, 1 ≤ k → k ≤ N + 1 → ∀ x : ℝ, |iteratedDeriv k Y x| ≤ M) →
      (∀ k, k ≤ N → ∀ x : ℝ,
        |iteratedDeriv k H x| ≤ M ∧ |iteratedDeriv k (fun t => (H t)⁻¹) x| ≤ M) →
      (∀ k, 1 ≤ k → k ≤ N + 1 → ∀ x : ℝ,
        |iteratedDeriv k (Function.invFun Y) x| ≤ M) →
      ∀ (v : Atom) (x : ℝ), x ∈ Ioo (0 : ℝ) 1 → ∀ k, k ≤ N →
        |iteratedDeriv k (positiveReferenceGeometryScalar l r Y H v) x| ≤
          C * M ^ (2 * N + 2) := by
  obtain ⟨CP, hCP, hproduct⟩ := referencePotential_product_envelope N
  obtain ⟨CC, hCC, hcomposition⟩ := referencePotential_composition_envelope N
  let C : ℝ := CP * CC ^ 2
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le hCP (one_le_pow₀ hCC)
  refine ⟨C, hC, ?_⟩
  intro M hM l r hlr hwidth hwidthInv Y H hgeometry hYj hHj hχj v x hx k hk
  let χ : ℝ → ℝ := Function.invFun Y
  let a : ℝ → ℝ := fun t => l + (r - l) * t
  let b : ℝ → ℝ := fun t => (t - l) / (r - l)
  let Z : ℝ := CC * M * M ^ N
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hCC hM) (one_le_pow₀ hM)
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hMZ : M ≤ Z :=
    (le_mul_of_one_le_left hM0 hCC).trans
      (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hCC) hM0) (one_le_pow₀ hM))
  have hline : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hY : ContDiff ℝ ∞ Y := by
    simpa only [positiveReferenceCylinderChart, Function.comp_def] using
      hgeometry.chart_smooth.fst.comp hline
  have hH : ContDiff ℝ ∞ H := by
    simpa only [Function.comp_def] using hgeometry.height_smooth.comp hline
  have hχ : ContDiff ℝ ∞ χ := by
    simpa only [positiveReferenceCylinderInverse, Function.comp_def] using
      hgeometry.inverse_smooth.fst.comp hline
  have hHi : ContDiff ℝ ∞ (fun t => (H t)⁻¹) :=
    hH.inv (fun t => (hgeometry.height_positive (t, 0)).ne')
  have hYd : ContDiff ℝ ∞ (deriv Y) := (contDiff_infty_iff_deriv.mp hY).2
  have hχd : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have ha : ContDiff ℝ ∞ a := contDiff_const.add (contDiff_const.mul contDiff_id)
  have hb : ContDiff ℝ ∞ b := (contDiff_id.sub contDiff_const).div_const _
  have hwpos : 0 < r - l := sub_pos.mpr hlr
  have hax : a x ∈ Ioo l r := by
    dsimp only [a]
    constructor <;> nlinarith [mul_pos hwpos hx.1, mul_lt_mul_of_pos_left hx.2 hwpos]
  have hYx : Y (a x) ∈ Ioo (0 : ℝ) 1 :=
    (hgeometry.maps_open (x := (a x, 0)) ⟨hax, mem_univ _⟩).1
  have hχx : χ x ∈ Ioo l r :=
    (hgeometry.inverse_maps_open (x := (x, 0)) ⟨hx, mem_univ _⟩).1
  have hbx : |b (χ x)| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hχx.1.le) hwpos.le)]
    exact (div_le_one hwpos).mpr (sub_le_sub_right hχx.2.le l)
  have haj (k : ℕ) (hk : 1 ≤ k) (t : ℝ) : |iteratedDeriv k a t| ≤ M :=
    positiveReferenceGeometry_affine_jets hM0 l (r - l) t
      (by simpa only [abs_of_pos hwpos] using hwidth) k hk
  have hbj (k : ℕ) (hk : 1 ≤ k) (t : ℝ) : |iteratedDeriv k b t| ≤ M := by
    have he : b = fun u => -l / (r - l) + (r - l)⁻¹ * u := by
      funext u
      dsimp only [b]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [he]
    exact positiveReferenceGeometry_affine_jets hM0 _ _ t
      (by simpa only [abs_of_pos (inv_pos.mpr hwpos)] using hwidthInv) k hk
  have hYdj (k : ℕ) (hk : k ≤ N) (t : ℝ) : |iteratedDeriv k (deriv Y) t| ≤ M := by
    rw [← iteratedDeriv_succ']
    exact hYj (k + 1) (by omega) (by omega) t
  have hχdj (k : ℕ) (hk : k ≤ N) (t : ℝ) : |iteratedDeriv k (deriv χ) t| ≤ M := by
    rw [← iteratedDeriv_succ']
    exact hχj (k + 1) (by omega) (by omega) t
  have hphysical {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
      (hfj : ∀ k, k ≤ N → |iteratedDeriv k f (a x)| ≤ M) :
      ∀ k, k ≤ N → |iteratedDeriv k (f ∘ a) x| ≤ Z :=
    hcomposition hM0 hM f a x hf.contDiffAt ha.contDiffAt hfj
      (fun k hk _ => haj k hk x)
  have hcanonical {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
      (hfj : ∀ k, k ≤ N → |iteratedDeriv k f (χ x)| ≤ M) :
      ∀ k, k ≤ N → |iteratedDeriv k (f ∘ χ) x| ≤ Z :=
    hcomposition hM0 hM f χ x hf.contDiffAt hχ.contDiffAt hfj
      (fun k hk hkN => hχj k hk (by omega) x)
  have hYP := hphysical hY (fun k hk => by
    by_cases hk0 : k = 0
    · subst k
      simpa only [iteratedDeriv_zero, abs_of_pos hYx.1] using hYx.2.le.trans hM
    · exact hYj k (by omega) (by omega) (a x))
  have hIP := hcanonical hb (fun k hk => by
    by_cases hk0 : k = 0
    · subst k
      simpa only [iteratedDeriv_zero] using hbx.trans hM
    · exact hbj k (by omega) (χ x))
  have hHP := hphysical hH (fun k hk => (hHj k hk (a x)).1)
  have hHiP := hphysical hHi (fun k hk => (hHj k hk (a x)).2)
  have hJP := hphysical hYd (fun k hk => hYdj k hk (a x))
  have hHC := hcanonical hH (fun k hk => (hHj k hk (χ x)).1)
  have hHiC := hcanonical hHi (fun k hk => (hHj k hk (χ x)).2)
  have hJC := hcanonical hYd (fun k hk => hYdj k hk (χ x))
  have hJinverse (t : ℝ) : ∀ k, k ≤ N → |iteratedDeriv k (deriv χ ∘ Y) t| ≤ Z :=
    hcomposition hM0 hM (deriv χ) Y t hχd.contDiffAt hY.contDiffAt
      (fun k hk => hχdj k hk (Y t)) (fun k hk hkN => hYj k hk (by omega) t)
  have hJIP := hcomposition hZ0 hM (deriv χ ∘ Y) a x
    (hχd.comp hY).contDiffAt ha.contDiffAt (hJinverse (a x))
    (fun k hk _ => haj k hk x)
  have hS := hproduct hZ0 hM0 (H ∘ χ) (deriv χ) x
    (hH.comp hχ).contDiffAt hχd.contDiffAt hHC (fun k hk => hχdj k hk x)
  have hSI := hproduct hZ0 hZ0 ((fun t => (H t)⁻¹) ∘ χ) (deriv Y ∘ χ) x
    (hHi.comp hχ).contDiffAt (hYd.comp hχ).contDiffAt hHiC hJC
  have hZfinal : Z ≤ CP * Z * Z :=
    (le_mul_of_one_le_left hZ0 hCP).trans
      (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hCP) hZ0) hZ)
  have hdouble : CC * Z * M ^ N ≤ CP * Z * Z := by
    have hh : CC * M ^ N ≤ Z := by
      calc
        _ = (CC * 1) * M ^ N := by ring
        _ ≤ (CC * M) * M ^ N := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hM (zero_le_one.trans hCC)) (pow_nonneg hM0 _)
    calc
      _ = (CC * M ^ N) * Z := by ring
      _ ≤ Z * Z := mul_le_mul_of_nonneg_right hh hZ0
      _ ≤ CP * Z * Z := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left hZ0 hCP) hZ0
  have hsourceCost : CP * Z * M ≤ CP * Z * Z :=
    mul_le_mul_of_nonneg_left hMZ (mul_nonneg (zero_le_one.trans hCP) hZ0)
  have hcost : CP * Z * Z = C * M ^ (2 * N + 2) := by
    have hp : (M * M ^ N) ^ 2 = M ^ (2 * N + 2) := by
      rw [← pow_succ', ← pow_mul]
      congr 1 <;> omega
    calc
      _ = C * (M * M ^ N) ^ 2 := by dsimp only [C, Z]; ring
      _ = _ := by rw [hp]
  have hzero : 0 ≤ CP * Z * Z :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hCP) hZ0) hZ0
  rw [← hcost]
  cases v
  case chartRadial => exact (hYP k hk).trans hZfinal
  case inverseRadial => exact (hIP k hk).trans hZfinal
  case height => exact (hHP k hk).trans hZfinal
  case heightInverse => exact (hHiP k hk).trans hZfinal
  case jacobian => exact (hJP k hk).trans hZfinal
  case jacobianInverse => exact (hJIP k hk).trans hdouble
  case sourceFactor => exact (hS k hk).trans hsourceCost
  case sourceFactorInverse => exact hSI k hk
  all_goals simpa only [positiveReferenceGeometryScalar, iteratedDeriv_fun_const_zero, abs_zero]
    using hzero

end ContinuousFlexibility.Analysis
