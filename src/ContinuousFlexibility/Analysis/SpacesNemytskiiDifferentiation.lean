import ContinuousFlexibility.Analysis.SpacesNemytskiiPartials

/-!
# Differentiating normalized composition terms

The chain and product rules give a finite sum of terms of the same form.
Each spatial differentiation raises the recorded derivative budget by
at most one and preserves exactly one occurrence of every direction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem SpacesRadialMultiplier.sliceDerivative {T : MaterialData} {α : ℝ} {A : ℝ → ℝ}
    (hA : SpacesRadialMultiplier T α A) (radial : Bool) :
    SpacesRadialMultiplier T α (spacesRadialSliceDerivative A radial) := by
  cases radial
  · exact spacesRadialMultiplier_zero T α
  · exact hA.deriv

namespace SpacesNemytskiiTerm

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {k : ℕ}

def chainWeightDerivative (hT : IsMaterialData D T) (t : SpacesNemytskiiTerm T γ k)
    (radial : Bool) : SpacesNemytskiiTerm T γ k :=
  t.addBaseFactor hT (0, 0) (spacesRadialSliceDerivative (fun x => T.H (T.radius x) ^ γ) radial)
    ((spacesRadialMultiplier_materialH hT γ).sliceDerivative radial)

def chainBaseDerivative (hT : IsMaterialData D T) (t : SpacesNemytskiiTerm T γ k)
    (radial : Bool) : SpacesNemytskiiTerm T γ k :=
  t.addBaseFactor hT (spacesJetOrderSucc radial (0, 0)) (fun x => T.H (T.radius x) ^ γ)
    (spacesRadialMultiplier_materialH hT γ)

@[simp] theorem chainWeightDerivative_order (hT : IsMaterialData D T)
    (t : SpacesNemytskiiTerm T γ k) (radial : Bool) :
    (t.chainWeightDerivative hT radial).order = t.order := by
  rw [chainWeightDerivative, addBaseFactor_order]
  simp only [add_zero]

@[simp] theorem chainBaseDerivative_order (hT : IsMaterialData D T)
    (t : SpacesNemytskiiTerm T γ k) (radial : Bool) :
    (t.chainBaseDerivative hT radial).order = t.order + 1 := by
  rw [chainBaseDerivative, addBaseFactor_order, spacesJetOrderSucc_total]
  rfl

theorem evaluate_partial (hT : IsMaterialData D T) (t : SpacesNemytskiiTerm T γ k)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u)
    {v : Fin k → PolarPoint → ℝ} (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (radial : Bool) (p : PolarPoint) :
    spacesPartial radial (t.evaluate F u v) p =
      (t.coefficientDerivative radial).evaluate F u v p +
      (t.chainWeightDerivative hT radial).evaluate F u v p +
      (t.chainBaseDerivative hT radial).evaluate F u v p +
      (∑ i, (t.baseDerivative i radial).evaluate F u v p) +
      ∑ i, (t.directionDerivative i radial).evaluate F u v p := by
  let H (x : ℝ) := T.H (T.radius x) ^ γ
  have hH := (spacesRadialMultiplier_materialH hT γ).contDiff
  have hA := spaces_radial_slice_hasDerivAt t.coefficient_mem.contDiff radial p
  have harg := (spaces_radial_slice_hasDerivAt hH radial p).mul (spaces_slice_hasDerivAt hu radial p)
  simp only [spacesJetSlice_self] at harg
  have hFd : HasDerivAt (iteratedDeriv (k + t.baseFactors) F)
      (iteratedDeriv (k + t.baseFactors + 1) F (H p.1 * u p)) (H p.1 * u p) := by
    rw [iteratedDeriv_succ]
    exact ((spaces_scalar_contDiff_iteratedDeriv hF _).differentiable (by simp) _).hasDerivAt
  have hcomp := hFd.comp_of_eq (spacesJetSlicePoint radial p) harg
    (by simp only [Pi.mul_apply, spacesJetSlice_self, H])
  have hU := spaces_jet_product_slice_hasDerivAt t.baseOrder (fun _ => hu) radial p
  have hV := spaces_jet_product_slice_hasDerivAt t.directionOrder hv radial p
  have h := ((hA.mul hcomp).mul hU).mul hV
  simp only [Pi.mul_apply, Function.comp_apply, spacesJetSlice_self] at h
  change HasDerivAt (fun x => t.evaluate F u v (spacesJetSlice radial p x)) _ _ at h
  rw [spacesPartial_eq_slice_deriv (t.evaluate_contDiff hT hF hu hv), h.deriv]
  have hzero : mixedDerivative 0 0 u p = u p := by simp only [mixedDerivative, iteratedDeriv_zero]
  have hsumU :
      (t.coefficient p.1 * iteratedDeriv (k + t.baseFactors) F (H p.1 * u p)) *
        (∑ i, ∏ j, mixedDerivative
          (Function.update t.baseOrder i (spacesJetOrderSucc radial (t.baseOrder i)) j).1
          (Function.update t.baseOrder i (spacesJetOrderSucc radial (t.baseOrder i)) j).2 u p) *
        (∏ i, mixedDerivative (t.directionOrder i).1 (t.directionOrder i).2 (v i) p) =
        ∑ i, (t.baseDerivative i radial).evaluate F u v p := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hsumV :
      (t.coefficient p.1 * iteratedDeriv (k + t.baseFactors) F (H p.1 * u p)) *
        (∏ i, mixedDerivative (t.baseOrder i).1 (t.baseOrder i).2 u p) *
        (∑ i, ∏ j, mixedDerivative
          (Function.update t.directionOrder i (spacesJetOrderSucc radial (t.directionOrder i)) j).1
          (Function.update t.directionOrder i (spacesJetOrderSucc radial (t.directionOrder i)) j).2 (v j) p) =
        ∑ i, (t.directionDerivative i radial).evaluate F u v p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  rw [← hsumU, ← hsumV]
  simp only [evaluate, coefficientDerivative, chainWeightDerivative, chainBaseDerivative,
    addBaseFactor, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, hzero, Nat.add_assoc]
  change _ = _
  cases radial <;> simp only [spacesRadialSliceDerivative, Bool.false_eq_true, ite_false, ite_true, H] <;> ring

end SpacesNemytskiiTerm

end ContinuousFlexibility.Statements
