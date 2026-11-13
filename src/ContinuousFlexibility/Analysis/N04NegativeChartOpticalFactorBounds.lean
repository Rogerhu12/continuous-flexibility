import ContinuousFlexibility.Analysis.N04RealizationLeadStart
import ContinuousFlexibility.Analysis.ActualNegativeOpticalRootDivision
import ContinuousFlexibility.Analysis.PositivePowerPolynomialMaterialJets
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# Reference optical factors on the actual negative halves

The smooth optical division is chosen once before every power and jet
order. The original full-half division theorem supplies its reciprocal
bound at the sample stored by the actual atlas. Applying the polynomial
power calculus at the zero auxiliary state introduces no collar radius.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- The width is the actual optical half, with the reference cut already
chosen by the retained start. -/
def negativeOpticalWidth (m : ℕ) (side : Bool) : ℝ :=
  n04bNegativeRight W.C (n04bActualReferenceCut W.through03) (m, side) -
    n04bNegativeLeft W.C (n04bActualReferenceCut W.through03) (m, side)

theorem negativeOpticalWidth_pos (m : ℕ) (side : Bool) :
    0 < W.negativeOpticalWidth m side := by
  have hc := n04bActualReferenceCut_mem W.through03 m
  cases side <;> simp only [negativeOpticalWidth, n04bNegativeRight,
    n04bNegativeLeft, Bool.false_eq_true, ↓reduceIte]
  · exact sub_pos.mpr hc.1
  · exact sub_pos.mpr hc.2

theorem negativeOpticalWidth_le_component (m : ℕ) (side : Bool) :
    W.negativeOpticalWidth m side ≤ W.C.right m - W.C.left m := by
  have hc := n04bActualReferenceCut_mem W.through03 m
  cases side <;> simp only [negativeOpticalWidth, n04bNegativeRight,
    n04bNegativeLeft, Bool.false_eq_true, ↓reduceIte] <;> linarith only [hc.1, hc.2]

/-- One actual reference optical division controls every real power,
including the positive square root used in the regularized flow. All
constants precede the component, endpoint and physical point. -/
theorem negativeOpticalFactor_power_material_jets (e : ℕ ≃ N04PieceIndex W.D) :
    ∃ g : ℕ → Bool → ℝ → ℝ,
      (∀ m side, ContDiff ℝ ∞ (g m side)) ∧
      (∀ m side t, t ∈ Icc (0 : ℝ) (W.C.right m - W.C.left m) →
        n01aOpticalRadicand W.D.w
          (inwardComponentPoint (W.C.left m) (W.C.right m) side t) = t * g m side t) ∧
      (∀ m side t, t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) → 0 < g m side t) ∧
      ∀ a : ℝ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
        ∀ m side t, t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) → ∀ n,
          |iteratedDeriv n (fun x => g m side x ^ a) t| ≤
            B n * W.T.E0
              (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (B n) := by
  classical
  obtain ⟨K₀, hK₀, hoptical⟩ := W.primitive.2.2
  obtain ⟨Ag, Pg, hAg, hPg, Bg, Qg, hBg, hQg, hdivision⟩ :=
    n04bActualTypedAtlas_opticalRootDivision_half_material
      W.hT W.hS W.through03 W.field e hK₀
  choose g hg hfactor hjet hvalue using
    fun (m : ℕ) (side : Bool) =>
      hdivision (e.symm (.inl (m, side))) m side (e.apply_symm_apply _)
        (W.C.cell m) (W.host m) (hoptical m)
  let A : ℕ → ℝ := fun n => 1 + Ag n + Pg n
  have hA (n : ℕ) : 1 ≤ A n := by
    dsimp only [A]
    linarith only [hAg n, hPg n]
  have hAgA (n : ℕ) : Ag n ≤ A n := by
    dsimp only [A]
    linarith only [hPg n]
  have hPgA (n : ℕ) : Pg n ≤ A n := by
    dsimp only [A]
    linarith only [hAg n]
  let M : ℝ := 1 + A 0 + Bg + Qg
  have hM : 1 ≤ M := by
    dsimp only [M]
    linarith only [hA 0, hBg, hQg]
  have hA0M : A 0 ≤ M := by
    dsimp only [M]
    linarith only [hBg, hQg]
  have hBgM : Bg ≤ M := by
    dsimp only [M]
    linarith only [hA 0, hQg]
  have hQgM : Qg ≤ M := by
    dsimp only [M]
    linarith only [hA 0, hBg]
  have hp : Monotone realGrading := fun _ _ _ => le_rfl
  obtain ⟨base, loss, hmaterial⟩ := positivePower_polynomial_material_bound
    (X := ℝ) hp coordinate_hasInterpolation_realGrading 0
  refine ⟨g, hg, hfactor, (fun m side t ht => (hvalue m side t ht).1), ?_⟩
  intro a
  obtain ⟨B, hB, hbound⟩ := hmaterial a M hM A hA
  refine ⟨B, hB, ?_⟩
  intro m side t ht n
  let E : ℝ := W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side)))))
  have hE : 1 ≤ E := W.floor _
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have htfull : t ∈ Icc (0 : ℝ) (W.C.right m - W.C.left m) :=
    ⟨ht.1, ht.2.trans (W.negativeOpticalWidth_le_component m side)⟩
  have hj (k : ℕ) : |iteratedDeriv k (g m side) t| ≤ A k * E ^ (A k) :=
    (hjet m side k t htfull).trans
      (mul_le_mul (hAgA k) (Real.rpow_le_rpow_of_exponent_le hE (hPgA k))
        (Real.rpow_nonneg hE0 _) (zero_le_one.trans (hA k)))
  have hv := hvalue m side t ht
  have hvUpper : g m side t ≤ M * E ^ M := by
    have hb : |g m side t| ≤ A 0 * E ^ (A 0) := by
      simpa only [iteratedDeriv_zero] using hj 0
    exact ((le_abs_self _).trans hb).trans
      (mul_le_mul hA0M (Real.rpow_le_rpow_of_exponent_le hE hA0M)
        (Real.rpow_nonneg hE0 _) (zero_le_one.trans hM))
  have hvInverse : (g m side t)⁻¹ ≤ M * E ^ M :=
    hv.2.trans (mul_le_mul hBgM (Real.rpow_le_rpow_of_exponent_le hE hQgM)
      (Real.rpow_nonneg hE0 _) (zero_le_one.trans hM))
  have hz : realGrading base (0 : ℝ) ≤ 1 := by
    simpa only [map_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
  have hinner (k : ℕ) (_hk : 1 ≤ k) :
      ‖iteratedFDeriv ℝ k (g m side) t‖ ≤
        A k * E ^ (A k) * (1 + realGrading (k + 0) (0 : ℝ)) := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      map_zero, add_zero, mul_one] using hj k
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    map_zero, add_zero, mul_one] using
    hbound (0 : ℝ) hz E hE (g m side) t (hg m side).contDiffAt
      hv.1 hvUpper hvInverse hinner n

end N04RealizationStart

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeOpticalFactor_power_material_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeOpticalFactor_power_material_jets
