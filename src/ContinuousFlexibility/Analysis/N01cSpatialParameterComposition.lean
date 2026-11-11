import ContinuousFlexibility.Analysis.N01cParameterCalculus
import ContinuousFlexibility.Analysis.N01cStateSeminorms
import ContinuousFlexibility.Analysis.CylinderMixedJets
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Actual spatial composition jets with smooth parameter towers

A spatial Faà di Bruno formula is obtained from uniqueness of the genuine
projective towers of the normed spatial maps. Every partition summand is a
smooth function of its base input and the finitely many actual spatial
input jets. This gives parameter towers of every mixed spatial derivative,
without assuming joint normability of the parameter space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

section ParameterTuples

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def smoothDirections_vectorTuple {m : ℕ} {U : Set X} {f : Fin m → X → Y}
    (hU : IsOpen U) (J : ∀ i, SmoothDirections U (f i)) :
    SmoothDirections U (fun x i => f i x) where
  open_domain := hU
  D := fun n x => ContinuousMultilinearMap.pi (fun i => (J i).D n x)
  zero := by
    intro x hx
    funext i
    rw [ContinuousMultilinearMap.pi_apply, (J i).zero x hx]
  continuous := by
    intro n
    apply continuousOn_pi.mpr
    intro i
    simpa only [ContinuousMultilinearMap.pi_apply] using (J i).continuous n
  derivative := by
    intro n x hx v w
    unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      Pi.smul_apply, Pi.sub_apply, ContinuousMultilinearMap.pi_apply] using
      (J i).derivative n x hx v w

def smoothDirections_finiteSum {ι : Type*} [Fintype ι]
    {U : Set X} {f : ι → X → Y} (hU : IsOpen U)
    (J : ∀ i, SmoothDirections U (f i)) :
    SmoothDirections U (fun x => ∑ i, f i x) where
  open_domain := hU
  D := fun n x => ∑ i, (J i).D n x
  zero := by
    intro x hx
    simp only [ContinuousMultilinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => (J i).zero x hx)
  continuous := by
    intro n
    simpa only [ContinuousMultilinearMap.sum_apply] using
      continuousOn_finsetSum Finset.univ (fun i _ => (J i).continuous n)
  derivative := by
    intro n x hx v w
    have hd := HasProjectiveCurveDerivAt.finset_sum Finset.univ
      (fun i _ => (J i).derivative n x hx v w)
    simpa only [HasProjectiveLineDerivAt, ContinuousMultilinearMap.sum_apply] using hd

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

def smoothDirections_constant {U : Set X} (hU : IsOpen U) (c : Y) :
    SmoothDirections U (fun _ : X => c) := by
  let J := (smoothDirectionsLinear (0 : X →L[ℝ] ℝ)).restrict hU (subset_univ _)
  let K := smoothDirections_contDiff_comp (g := fun _ : ℝ => c)
    J isOpen_univ contDiff_const.contDiffOn (fun _ _ => mem_univ _)
  exact K.congr (fun _ _ => rfl)

end ParameterTuples

section NormedSpatialComposition

variable {E Y Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Evaluation of a variable multilinear map is a continuous polynomial. -/
theorem contDiff_multilinearEvaluation (n : ℕ) :
    ContDiff ℝ ∞ (fun z : (Y [×n]→L[ℝ] Z) × (Fin n → Y) => z.1 z.2) := by
  let L : (Y [×n]→L[ℝ] Z) →L[ℝ] (Y [×n]→L[ℝ] Z) :=
    ContinuousLinearMap.id ℝ _
  have hdiag : ContDiff ℝ ∞
      (fun z : (Y [×n]→L[ℝ] Z) × (Fin n → Y) =>
        fun _ : Option (Fin n) => z) :=
    contDiff_pi.mpr (fun _ => contDiff_id)
  have h := L.continuousMultilinearMapOption.contDiff.comp hdiag
  simpa only [ContinuousLinearMap.continuousMultilinearMapOption_apply_eq_self,
    L, ContinuousLinearMap.id_apply, Function.comp_def] using h

/-- The normed spatial derivatives equal the actual ordered-partition
tower. This equality follows from the derivative recurrence and uniqueness. -/
theorem iteratedFDeriv_comp_ordered_apply
    {Ω : Set E} {V : Set Y} {u : E → Y} {g : Y → Z}
    (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u Ω) (hg : ContDiffOn ℝ ∞ g V)
    (hmap : MapsTo u Ω V) (n : ℕ) {p : E} (hp : p ∈ Ω) (v : Fin n → E) :
    iteratedFDeriv ℝ n (g ∘ u) p v =
      ∑ c : OrderedFinpartition n,
        iteratedFDeriv ℝ c.length g (u p)
          (fun i => iteratedFDeriv ℝ (c.partSize i) u p (v ∘ c.emb i)) := by
  have hactual := hasProjectiveJetsOn_of_contDiffOn hΩ (hg.comp hu hmap)
  have hcomposed := hasProjectiveJetsOn_contDiff_comp hΩ hV
    (hasProjectiveJetsOn_of_contDiffOn hΩ hu) hg hmap
  have heq := HasProjectiveJetsOn.unique hΩ hactual hcomposed n p hp
  have heval := congrArg (fun A : E [×n]→L[ℝ] Z => A v) heq
  simpa only [projectiveCompositionJets_apply, projectiveCompositionTerm_apply] using heval

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- A parameter tower for one true spatial composition jet. Only the
actual spatial input evaluations used by its partitions are supplied. -/
def smoothDirections_spatialFDeriv_comp
    {U : Set X} {Ω : Set E} {V : Set Y} {u : X → E → Y} {g : Y → Z}
    (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hu : ∀ x ∈ U, ContDiffOn ℝ ∞ (u x) Ω)
    (hg : ContDiffOn ℝ ∞ g V) (hmap : ∀ x ∈ U, MapsTo (u x) Ω V)
    (n : ℕ) (p : E) (hp : p ∈ Ω) (v : Fin n → E)
    (J0 : SmoothDirections U (fun x => u x p))
    (Jjet : ∀ c : OrderedFinpartition n, ∀ i : Fin c.length,
      SmoothDirections U
        (fun x => iteratedFDeriv ℝ (c.partSize i) (u x) p (v ∘ c.emb i))) :
    SmoothDirections U (fun x => iteratedFDeriv ℝ n (g ∘ u x) p v) := by
  let F : OrderedFinpartition n → X → Z := fun c x =>
    iteratedFDeriv ℝ c.length g (u x p)
      (fun i => iteratedFDeriv ℝ (c.partSize i) (u x) p (v ∘ c.emb i))
  have JT : ∀ c, SmoothDirections U (F c) := by
    intro c
    let f : Fin (c.length + 1) → X → Y :=
      Fin.cons (fun x => u x p)
        (fun i x => iteratedFDeriv ℝ (c.partSize i) (u x) p (v ∘ c.emb i))
    let Jf : ∀ j, SmoothDirections U (f j) :=
      Fin.cases J0 (fun i => Jjet c i)
    let J := smoothDirections_vectorTuple J0.open_domain Jf
    let W : Set (Fin (c.length + 1) → Y) := {y | y 0 ∈ V}
    have hW : IsOpen W := hV.preimage (continuous_apply 0)
    let H : (Fin (c.length + 1) → Y) → Z :=
      fun y => iteratedFDeriv ℝ c.length g (y 0) (Fin.tail y)
    have hH : ContDiffOn ℝ ∞ H W := by
      intro y hy
      have houter : ContDiffAt ℝ ∞
          (fun t : Fin (c.length + 1) → Y => iteratedFDeriv ℝ c.length g (t 0)) y :=
        ((hg.contDiffAt (hV.mem_nhds hy)).iteratedFDeriv_right (by simp)).comp y
          (contDiffAt_apply ℝ Y 0 y)
      have htail : ContDiffAt ℝ ∞ (fun t : Fin (c.length + 1) → Y => Fin.tail t) y := by
        apply contDiffAt_pi.mpr
        intro i
        exact contDiffAt_apply ℝ Y i.succ y
      exact ((contDiff_multilinearEvaluation (Y := Y) (Z := Z) c.length).contDiffAt.comp y
        (houter.prodMk htail)).contDiffWithinAt
    have hm : MapsTo (fun x j => f j x) U W := by
      intro x hx
      exact hmap x hx hp
    let K := smoothDirections_contDiff_comp J hW hH hm
    refine K.congr (fun x hx => ?_)
    have he : (fun j => f j x) = Fin.cons (u x p)
        (fun i => iteratedFDeriv ℝ (c.partSize i) (u x) p (v ∘ c.emb i)) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    change H (fun j => f j x) = F c x
    rw [he]
    simp only [H, F, Fin.cons_zero, Fin.tail_cons]
  let Jsum := smoothDirections_finiteSum J0.open_domain JT
  exact Jsum.congr (fun x hx =>
    (iteratedFDeriv_comp_ordered_apply hΩ hV (hu x hx) hg (hmap x hx) n hp v).symm)

end NormedSpatialComposition

/-- A coordinate word with exactly a radial and b angular slots. -/
def cylinderMixedWord (a b : ℕ) : Fin (a + b) → Fin 2 :=
  Fin.append (fun _ : Fin a => 0) (fun _ : Fin b => 1)

theorem cylinderMixedWord_radial_count (a b : ℕ) :
    (∑ i, if cylinderMixedWord a b i = 0 then 1 else 0) = a := by
  rw [Fin.sum_univ_add]
  simp only [cylinderMixedWord, Fin.append_left, Fin.append_right, ite_true,
    one_ne_zero, ite_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, mul_one, mul_zero, add_zero]

theorem cylinderMixedWord_angular_count (a b : ℕ) :
    (∑ i, if cylinderMixedWord a b i = 0 then 0 else 1) = b := by
  rw [Fin.sum_univ_add]
  simp only [cylinderMixedWord, Fin.append_left, Fin.append_right, ite_true,
    one_ne_zero, ite_false, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_one, zero_add]

theorem mixedDerivative_eq_iteratedFDeriv_word
    {Ω : Set PolarPoint} {f : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ Ω) :
    mixedDerivative a b f p =
      iteratedFDeriv ℝ (a + b) f p (fun i => cylinderBasisVector (cylinderMixedWord a b i)) := by
  simpa only [cylinderMixedWord_radial_count, cylinderMixedWord_angular_count] using
    (iteratedFDeriv_cylinderBasis_eq_mixedDerivative hΩ hf (a + b) hp
      (cylinderMixedWord a b)).symm

/-- Spatial equality on the open set transfers every actual mixed jet. -/
theorem mixedDerivative_eq_of_eqOn
    {Ω : Set PolarPoint} {f g : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (he : EqOn f g Ω) (a b : ℕ) {p : PolarPoint} (hp : p ∈ Ω) :
    mixedDerivative a b f p = mixedDerivative a b g p := by
  have hev : f =ᶠ[𝓝 p] g := by
    filter_upwards [hΩ.mem_nhds hp] with q hq
    exact he hq
  rw [mixedDerivative_eq_iteratedFDeriv_word hΩ hf a b hp,
    mixedDerivative_eq_iteratedFDeriv_word hΩ hg a b hp,
    (hev.iteratedFDeriv ℝ (a + b)).eq_of_nhds]

section FiniteScalarInputs

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  {m : ℕ} {U : Set X} {Ω : Set PolarPoint} {V : Set (Fin m → ℝ)}
  {u : X → PolarPoint → Fin m → ℝ} {g : (Fin m → ℝ) → ℝ}

/-- Componentwise mixed spatial jets give the actual vector-valued
Fréchet jet evaluated on any coordinate word. -/
def smoothDirections_spatialBasisJet
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hu : ∀ x ∈ U, ContDiffOn ℝ ∞ (u x) Ω)
    (p : PolarPoint) (hp : p ∈ Ω)
    (J : ∀ a b : ℕ, ∀ j : Fin m,
      SmoothDirections U (fun x => mixedDerivative a b (fun q => u x q j) p))
    (n : ℕ) (w : Fin n → Fin 2) :
    SmoothDirections U
      (fun x => iteratedFDeriv ℝ n (u x) p (fun i => cylinderBasisVector (w i))) := by
  let a : ℕ := ∑ i, if w i = 0 then 1 else 0
  let b : ℕ := ∑ i, if w i = 0 then 0 else 1
  let K := smoothDirections_scalarTuple hU (J a b)
  refine K.congr (fun x hx => ?_)
  funext j
  let L : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hL := L.iteratedFDeriv_comp_left ((hu x hx).contDiffAt (hΩ.mem_nhds hp))
    (i := n) (by simp)
  have hLeval := congrArg (fun A : PolarPoint [×n]→L[ℝ] ℝ =>
    A (fun i => cylinderBasisVector (w i))) hL
  have hcomp : iteratedFDeriv ℝ n (fun q => u x q j) p
      (fun i => cylinderBasisVector (w i)) =
        (iteratedFDeriv ℝ n (u x) p (fun i => cylinderBasisVector (w i))) j := by
    simpa only [L, Function.comp_def, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe] using hLeval
  have hj : ContDiffOn ℝ ∞ (fun q => u x q j) Ω :=
    (contDiffOn_pi.mp (hu x hx)) j
  exact (iteratedFDeriv_cylinderBasis_eq_mixedDerivative hΩ hj n hp w).symm.trans hcomp

/-- Every mixed spatial derivative of a finite-dimensional smooth
composition has a genuine parameter tower, assembled from its actual
mixed input jets. -/
def smoothDirections_mixedDerivative_comp
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hu : ∀ x ∈ U, ContDiffOn ℝ ∞ (u x) Ω)
    (hg : ContDiffOn ℝ ∞ g V) (hmap : ∀ x ∈ U, MapsTo (u x) Ω V)
    (p : PolarPoint) (hp : p ∈ Ω)
    (J : ∀ a b : ℕ, ∀ j : Fin m,
      SmoothDirections U (fun x => mixedDerivative a b (fun q => u x q j) p))
    (a b : ℕ) :
    SmoothDirections U (fun x => mixedDerivative a b (g ∘ u x) p) := by
  let w := cylinderMixedWord a b
  let v : Fin (a + b) → PolarPoint := fun i => cylinderBasisVector (w i)
  let J0₀ := smoothDirections_scalarTuple hU (J 0 0)
  let J0 : SmoothDirections U (fun x => u x p) :=
    J0₀.congr (fun x _ => by funext j; simp only [mixedDerivative, iteratedDeriv_zero])
  let Jjet : ∀ c : OrderedFinpartition (a + b), ∀ i : Fin c.length,
      SmoothDirections U
        (fun x => iteratedFDeriv ℝ (c.partSize i) (u x) p (v ∘ c.emb i)) :=
    fun c i => smoothDirections_spatialBasisJet hU hΩ hu p hp J
      (c.partSize i) (w ∘ c.emb i)
  let K := smoothDirections_spatialFDeriv_comp hΩ hV hu hg hmap (a + b) p hp v J0 Jjet
  exact K.congr (fun x hx =>
    (mixedDerivative_eq_iteratedFDeriv_word hΩ (hg.comp (hu x hx) (hmap x hx)) a b hp).symm)

end FiniteScalarInputs


/-- The exact spatial partition formula, with its coordinate word fixed. -/
theorem mixedDerivative_comp_ordered
    {m : ℕ} {Ω : Set PolarPoint} {V : Set (Fin m → ℝ)}
    {u : PolarPoint → Fin m → ℝ} {g : (Fin m → ℝ) → ℝ}
    (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hu : ContDiffOn ℝ ∞ u Ω) (hg : ContDiffOn ℝ ∞ g V)
    (hmap : MapsTo u Ω V) (a b : ℕ) {p : PolarPoint} (hp : p ∈ Ω) :
    mixedDerivative a b (g ∘ u) p =
      ∑ c : OrderedFinpartition (a + b),
        iteratedFDeriv ℝ c.length g (u p)
          (fun i => iteratedFDeriv ℝ (c.partSize i) u p
            (fun j => cylinderBasisVector (cylinderMixedWord a b (c.emb i j)))) := by
  rw [mixedDerivative_eq_iteratedFDeriv_word hΩ (hg.comp hu hmap) a b hp]
  exact iteratedFDeriv_comp_ordered_apply hΩ hV hu hg hmap (a + b) hp
    (fun j => cylinderBasisVector (cylinderMixedWord a b j))

/-- Subtraction commutes with the actual mixed jets on an open set. -/
theorem mixedDerivative_sub_of_contDiffOn
    {Ω : Set PolarPoint} {f g : PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ Ω) :
    mixedDerivative a b (fun q => f q - g q) p =
      mixedDerivative a b f p - mixedDerivative a b g p := by
  have hdf : ContDiffAt ℝ (a + b) f p :=
    (hf.contDiffAt (hΩ.mem_nhds hp)).of_le (by simp)
  have hdg : ContDiffAt ℝ (a + b) g p :=
    (hg.contDiffAt (hΩ.mem_nhds hp)).of_le (by simp)
  rw [mixedDerivative_eq_iteratedFDeriv_word hΩ (hf.sub hg) a b hp,
    mixedDerivative_eq_iteratedFDeriv_word hΩ hf a b hp,
    mixedDerivative_eq_iteratedFDeriv_word hΩ hg a b hp]
  have hsub : iteratedFDeriv ℝ (a + b) (fun q => f q - g q) p =
      iteratedFDeriv ℝ (a + b) f p - iteratedFDeriv ℝ (a + b) g p := by
    simpa only [Pi.sub_def] using
      (iteratedFDeriv_sub_apply (i := a + b) hdf hdg)
  have hvalue := congrArg (fun A : PolarPoint [×(a + b)]→L[ℝ] ℝ =>
    A (fun i => cylinderBasisVector (cylinderMixedWord a b i))) hsub
  simpa only [ContinuousMultilinearMap.sub_apply] using hvalue

/-- Subtracting a fixed spatial reference field preserves the genuine
parameter tower for every actual mixed derivative. -/
def smoothDirections_mixedDifference
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {Ω : Set PolarPoint} {f : X → PolarPoint → ℝ}
    (hΩ : IsOpen Ω) (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) Ω)
    (x0 : X) (hx0 : x0 ∈ U) (a b : ℕ) (p : PolarPoint) (hp : p ∈ Ω)
    (J : SmoothDirections U (fun x => mixedDerivative a b (f x) p)) :
    SmoothDirections U
      (fun x => mixedDerivative a b (fun q => f x q - f x0 q) p) := by
  let K := smoothDirectionsAdd J
    (smoothDirections_constant J.open_domain (-mixedDerivative a b (f x0) p))
  refine K.congr (fun x hx => ?_)
  rw [mixedDerivative_sub_of_contDiffOn hΩ (hf x hx) (hf x0 hx0) a b hp]
  exact (sub_eq_add_neg _ _).symm

end ContinuousFlexibility.Analysis
