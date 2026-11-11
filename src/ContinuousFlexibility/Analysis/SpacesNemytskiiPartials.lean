import ContinuousFlexibility.Analysis.SpacesNemytskiiTerms

/-!
# Coordinate differentiation of composition terms

The coordinate derivatives used in the finite jet expansion are actual
one-variable derivatives of slices. Finite products differentiate by
replacing one recorded jet order at a time.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def spacesJetSlice (radial : Bool) (p : PolarPoint) (x : ℝ) : PolarPoint :=
  if radial then (x, p.2) else (p.1, x)

def spacesJetSlicePoint (radial : Bool) (p : PolarPoint) : ℝ := if radial then p.1 else p.2

@[simp] theorem spacesJetSlice_self (radial : Bool) (p : PolarPoint) :
    spacesJetSlice radial p (spacesJetSlicePoint radial p) = p := by cases radial <;> rfl

theorem spacesJetSlice_contDiff (radial : Bool) (p : PolarPoint) : ContDiff ℝ ∞ (spacesJetSlice radial p) := by
  cases radial
  · exact contDiff_const.prodMk contDiff_id
  · exact contDiff_id.prodMk contDiff_const

def spacesPartial (radial : Bool) (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  if radial then radialPartial f p else angularPartial f p

theorem spacesPartial_eq_slice_deriv {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (radial : Bool) (p : PolarPoint) :
    spacesPartial radial f p = deriv (fun x => f (spacesJetSlice radial p x)) (spacesJetSlicePoint radial p) := by
  cases radial
  · exact (deriv_cylinder_angular_slice (hf.differentiable (by simp)) p.1 p.2).symm
  · exact (deriv_cylinder_radial_slice (hf.differentiable (by simp)) p.1 p.2).symm

theorem spaces_mixed_jet_slice_hasDerivAt {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (o : ℕ × ℕ) (radial : Bool) (p : PolarPoint) :
    HasDerivAt (fun x => mixedDerivative o.1 o.2 f (spacesJetSlice radial p x))
      (mixedDerivative (spacesJetOrderSucc radial o).1 (spacesJetOrderSucc radial o).2 f p)
      (spacesJetSlicePoint radial p) := by
  have hc := (contDiff_mixedDerivative hf o.1 o.2).comp (spacesJetSlice_contDiff radial p)
  have hd := (hc.differentiable (by simp) (spacesJetSlicePoint radial p)).hasDerivAt
  have he : deriv (fun x => mixedDerivative o.1 o.2 f (spacesJetSlice radial p x))
      (spacesJetSlicePoint radial p) =
      mixedDerivative (spacesJetOrderSucc radial o).1 (spacesJetOrderSucc radial o).2 f p := by
    cases radial
    · exact (deriv_cylinder_angular_slice
        ((contDiff_mixedDerivative hf o.1 o.2).differentiable (by simp)) p.1 p.2).trans
          (congrFun (angularPartial_mixedDerivative hf o.1 o.2) p)
    · exact (deriv_cylinder_radial_slice
        ((contDiff_mixedDerivative hf o.1 o.2).differentiable (by simp)) p.1 p.2).trans
          (congrFun (radialPartial_mixedDerivative hf o.1 o.2) p)
  exact he ▸ hd

theorem spaces_slice_hasDerivAt {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (radial : Bool) (p : PolarPoint) :
    HasDerivAt (fun x => f (spacesJetSlice radial p x))
      (mixedDerivative (spacesJetOrderSucc radial (0, 0)).1
        (spacesJetOrderSucc radial (0, 0)).2 f p) (spacesJetSlicePoint radial p) := by
  simpa only [mixedDerivative, iteratedDeriv_zero] using spaces_mixed_jet_slice_hasDerivAt hf (0, 0) radial p

def spacesRadialSliceDerivative (A : ℝ → ℝ) (radial : Bool) (x : ℝ) : ℝ :=
  if radial then deriv A x else 0

theorem spaces_radial_slice_hasDerivAt {A : ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (radial : Bool) (p : PolarPoint) :
    HasDerivAt (fun x => A (spacesJetSlice radial p x).1)
      (spacesRadialSliceDerivative A radial p.1) (spacesJetSlicePoint radial p) := by
  cases radial
  · change HasDerivAt (fun _ : ℝ => A p.1) 0 p.2
    exact hasDerivAt_const _ _
  · exact (hA.differentiable (by simp) p.1).hasDerivAt

theorem spaces_jet_product_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : ι → ℕ × ℕ) (u : ι → PolarPoint → ℝ) (i : ι) (o' : ℕ × ℕ) (p : PolarPoint) :
    (∏ j, mixedDerivative (Function.update o i o' j).1 (Function.update o i o' j).2 (u j) p) =
      mixedDerivative o'.1 o'.2 (u i) p *
        ∏ j ∈ Finset.univ.erase i, mixedDerivative (o j).1 (o j).2 (u j) p := by
  have he : (fun j => mixedDerivative (Function.update o i o' j).1
      (Function.update o i o' j).2 (u j) p) =
      Function.update (fun j => mixedDerivative (o j).1 (o j).2 (u j) p) i
        (mixedDerivative o'.1 o'.2 (u i) p) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]

theorem spaces_jet_product_slice_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : ι → ℕ × ℕ) {u : ι → PolarPoint → ℝ} (hu : ∀ i, ContDiff ℝ ∞ (u i))
    (radial : Bool) (p : PolarPoint) :
    HasDerivAt (fun x => ∏ i, mixedDerivative (o i).1 (o i).2 (u i) (spacesJetSlice radial p x))
      (∑ i, ∏ j, mixedDerivative
        (Function.update o i (spacesJetOrderSucc radial (o i)) j).1
        (Function.update o i (spacesJetOrderSucc radial (o i)) j).2 (u j) p)
      (spacesJetSlicePoint radial p) := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun i _ => spaces_mixed_jet_slice_hasDerivAt (hu i) (o i) radial p)
  simp only [spacesJetSlice_self, smul_eq_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [spaces_jet_product_update, mul_comm]

end ContinuousFlexibility.Statements
