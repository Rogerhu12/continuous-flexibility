import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus
import ContinuousFlexibility.Analysis.CylinderMixedJets
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Genuine mixed jets on a closed rectangle

The scalar jets are evaluations of the actual derivatives within the
closed rectangle. Their continuity, interior identification, and angular
trace derivatives follow from the within Taylor series. No extension is
assumed smooth on the other side of a boundary.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N07aClosedRectangleJets

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

def openRect (l r a b : ℝ) : Set PolarPoint := Ioo l r ×ˢ Ioo a b

def closedRect (l r a b : ℝ) : Set PolarPoint := Icc l r ×ˢ Icc a b

theorem open_subset_closed (l r a b : ℝ) :
    openRect l r a b ⊆ closedRect l r a b :=
  Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

theorem closure_openRect {l r a b : ℝ} (hlr : l < r) (hab : a < b) :
    closure (openRect l r a b) = closedRect l r a b := by
  simp only [openRect, closedRect, closure_prod_eq, closure_Ioo hlr.ne, closure_Ioo hab.ne]

theorem uniqueDiffOn_closedRect {l r a b : ℝ} (hlr : l < r) (hab : a < b) :
    UniqueDiffOn ℝ (closedRect l r a b) :=
  (uniqueDiffOn_Icc hlr).prod (uniqueDiffOn_Icc hab)

def word (i j : ℕ) : Fin (i + j) → Fin 2 :=
  Fin.addCases (fun _ : Fin i => 0) (fun _ : Fin j => 1)

theorem word_radial_sum (i j : ℕ) :
    (∑ k, if word i j k = 0 then 1 else 0) = i := by
  simp [word, Fin.sum_univ_add]

theorem word_angular_sum (i j : ℕ) :
    (∑ k, if word i j k = 0 then 0 else 1) = j := by
  simp [word, Fin.sum_univ_add]

def mixed (l r a b : ℝ) (u : PolarPoint → ℝ) (i j : ℕ) (p : PolarPoint) : ℝ :=
  iteratedFDerivWithin ℝ (i + j) u (closedRect l r a b) p
    (fun k => cylinderBasisVector (word i j k))

variable {l r a b : ℝ} {u : PolarPoint → ℝ}

theorem mixed_zero (p : PolarPoint) : mixed l r a b u 0 0 p = u p := by
  unfold mixed
  exact iteratedFDerivWithin_zero_apply _

theorem mixed_one_radial (hlr : l < r) (hab : a < b) {p : PolarPoint}
    (hp : p ∈ closedRect l r a b) :
    mixed l r a b u 1 0 p = fderivWithin ℝ u (closedRect l r a b) p (1, 0) := by
  simp only [mixed, Nat.add_zero,
    iteratedFDerivWithin_one_apply (uniqueDiffOn_closedRect hlr hab p hp)]
  congr 1

theorem continuousOn_mixed (hlr : l < r) (hab : a < b)
    (hu : ContDiffOn ℝ ∞ u (closedRect l r a b)) (i j : ℕ) :
    ContinuousOn (mixed l r a b u i j) (closedRect l r a b) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (i + j) => PolarPoint) ℝ
    (fun k => cylinderBasisVector (word i j k))).continuous.comp_continuousOn
      (hu.continuousOn_iteratedFDerivWithin (by simp) (uniqueDiffOn_closedRect hlr hab))

theorem mixed_agrees (hlr : l < r) (hab : a < b)
    (hu : ContDiffOn ℝ ∞ u (closedRect l r a b)) (i j : ℕ)
    {p : PolarPoint} (hp : p ∈ openRect l r a b) :
    mixed l r a b u i j p = mixedDerivative i j u p := by
  have hopen : ContDiffOn ℝ ∞ u (openRect l r a b) := hu.mono (open_subset_closed _ _ _ _)
  have hs : IsOpen (openRect l r a b) := isOpen_Ioo.prod isOpen_Ioo
  have hactual := iteratedFDerivWithin_eq_iteratedFDeriv
    (uniqueDiffOn_closedRect hlr hab)
    ((hopen.contDiffAt (hs.mem_nhds hp)).of_le (by simp : ((i + j : ℕ) : ℕ∞ω) ≤ ∞))
    (open_subset_closed _ _ _ _ hp)
  unfold mixed
  rw [hactual, iteratedFDeriv_cylinderBasis_eq_mixedDerivative hs hopen (i + j) hp,
    word_radial_sum, word_angular_sum]

/-- Coordinate-word permutation identities pass from the open rectangle
to its genuine closed Taylor jets by continuity. -/
theorem word_eq_mixed (hlr : l < r) (hab : a < b)
    (hu : ContDiffOn ℝ ∞ u (closedRect l r a b))
    (n : ℕ) (w : Fin n → Fin 2) {p : PolarPoint}
    (hp : p ∈ closedRect l r a b) :
    iteratedFDerivWithin ℝ n u (closedRect l r a b) p
        (fun k => cylinderBasisVector (w k)) =
      mixed l r a b u (∑ k, if w k = 0 then 1 else 0)
        (∑ k, if w k = 0 then 0 else 1) p := by
  have hopen : ContDiffOn ℝ ∞ u (openRect l r a b) := hu.mono (open_subset_closed _ _ _ _)
  have hs : IsOpen (openRect l r a b) := isOpen_Ioo.prod isOpen_Ioo
  have he : EqOn
      (fun q => iteratedFDerivWithin ℝ n u (closedRect l r a b) q
        (fun k => cylinderBasisVector (w k)))
      (mixed l r a b u (∑ k, if w k = 0 then 1 else 0)
        (∑ k, if w k = 0 then 0 else 1)) (openRect l r a b) := by
    intro q hq
    dsimp only
    have hactual := iteratedFDerivWithin_eq_iteratedFDeriv
      (uniqueDiffOn_closedRect hlr hab)
      ((hopen.contDiffAt (hs.mem_nhds hq)).of_le (by simp : (n : ℕ∞ω) ≤ ∞))
      (open_subset_closed _ _ _ _ hq)
    rw [hactual, iteratedFDeriv_cylinderBasis_eq_mixedDerivative hs hopen n hq,
      mixed_agrees hlr hab hu _ _ hq]
  have hcont : ContinuousOn
      (fun q => iteratedFDerivWithin ℝ n u (closedRect l r a b) q
        (fun k => cylinderBasisVector (w k))) (closedRect l r a b) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => PolarPoint) ℝ
      (fun k => cylinderBasisVector (w k))).continuous.comp_continuousOn
        (hu.continuousOn_iteratedFDerivWithin (by simp) (uniqueDiffOn_closedRect hlr hab))
  exact he.of_subset_closure hcont (continuousOn_mixed hlr hab hu _ _)
    (open_subset_closed _ _ _ _) (by rw [closure_openRect hlr hab]) hp

/-- Angular differentiation of a boundary trace is the next actual
closed mixed jet at every interior angular coordinate. -/
theorem mixed_angular_hasDerivAt (hlr : l < r) (hab : a < b)
    (hu : ContDiffOn ℝ ∞ u (closedRect l r a b)) (i j : ℕ)
    {t θ : ℝ} (ht : t ∈ Icc l r) (hθ : θ ∈ Ioo a b) :
    HasDerivAt (fun s => mixed l r a b u i j (t, s))
      (mixed l r a b u i (j + 1) (t, θ)) θ := by
  let n := i + j
  let v : Fin n → PolarPoint := fun k => cylinderBasisVector (word i j k)
  let w : Fin (n + 1) → Fin 2 := Fin.cons (1 : Fin 2) (word i j)
  let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => PolarPoint) ℝ v
  have hx : (t, θ) ∈ closedRect l r a b := ⟨ht, Ioo_subset_Icc_self hθ⟩
  have hn : (n : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
  have hd := (hu.ftaylorSeriesWithin (uniqueDiffOn_closedRect hlr hab)).fderivWithin n hn
    (t, θ) hx
  have hval := A.hasFDerivAt.comp_hasFDerivWithinAt (t, θ) hd
  have hslice : HasDerivWithinAt (fun s : ℝ => (t, s)) (0, 1) (Icc a b) θ :=
    ((hasDerivAt_const θ t).prodMk (hasDerivAt_id' θ)).hasDerivWithinAt
  have hangle := hval.comp_hasDerivWithinAt θ hslice (fun s hs => ⟨ht, hs⟩)
  change HasDerivWithinAt (fun s => mixed l r a b u i j (t, s))
    (iteratedFDerivWithin ℝ (n + 1) u (closedRect l r a b) (t, θ)
      (Fin.cons (0, 1) v)) (Icc a b) θ at hangle
  have hv : Fin.cons (0, 1) v =
      fun k => cylinderBasisVector (w k) := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp only [w, Fin.cons_zero, cylinderBasisVector,
        ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    · simp only [w, Fin.cons_succ, v]
  have hsort : iteratedFDerivWithin ℝ (n + 1) u (closedRect l r a b) (t, θ)
      (Fin.cons (0, 1) v) = mixed l r a b u i (j + 1) (t, θ) := by
    rw [hv]
    have h := word_eq_mixed hlr hab hu (n + 1) w hx
    simpa [w, Fin.sum_univ_succ, word, Fin.sum_univ_add, Nat.add_comm] using h
  rw [hsort] at hangle
  exact hangle.hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)

private def coordinate (v : PolarPoint) (j : Fin 2) : ℝ := if j = 0 then v.1 else v.2

private theorem sum_coordinates (v : PolarPoint) :
    (∑ j : Fin 2, coordinate v j • cylinderBasisVector j) = v := by
  rw [Fin.sum_univ_two]
  ext <;> simp [coordinate, cylinderBasisVector]

theorem multilinear_ext_coordinate_words {n : ℕ}
    (P Q : PolarPoint [×n]→L[ℝ] ℝ)
    (h : ∀ w : Fin n → Fin 2,
      P (fun i => cylinderBasisVector (w i)) = Q (fun i => cylinderBasisVector (w i))) :
    P = Q := by
  classical
  ext v
  have hexpand (F : PolarPoint [×n]→L[ℝ] ℝ) :
      F v = ∑ w : Fin n → Fin 2, (∏ i, coordinate (v i) (w i)) •
        F (fun i => cylinderBasisVector (w i)) := by
    have hv : (fun i : Fin n => ∑ j : Fin 2, coordinate (v i) j • cylinderBasisVector j) = v :=
      funext fun i => sum_coordinates (v i)
    have he := F.toMultilinearMap.map_sum
      (fun i : Fin n => fun j : Fin 2 => coordinate (v i) j • cylinderBasisVector j)
    change F (fun i => ∑ j : Fin 2, coordinate (v i) j • cylinderBasisVector j) =
      ∑ w : Fin n → Fin 2, F (fun i => coordinate (v i) (w i) • cylinderBasisVector (w i)) at he
    simpa only [hv, ContinuousMultilinearMap.map_smul_univ] using he
  rw [hexpand P, hexpand Q]
  exact Finset.sum_congr rfl fun w _ =>
    congrArg (fun t : ℝ => (∏ i, coordinate (v i) (w i)) • t) (h w)

end ContinuousFlexibility.Analysis.N07aClosedRectangleJets
