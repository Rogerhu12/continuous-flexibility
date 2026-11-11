import ContinuousFlexibility.Analysis.N01cTopologicalParameterIntegral
import ContinuousFlexibility.Analysis.N01cFlowParameterSmooth
import ContinuousFlexibility.Analysis.TameJetComposition

/-!
# Volterra solution maps on topological parameter spaces

Continuous multilinear maps are integrated by integrating their real
evaluations. This keeps the source topology unchanged. The resulting
Volterra map has joint continuity in parameters, time and all directions,
solves the actual linear time equation, and is its unique zero-initial
solution. No parameter derivative of a trajectory is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

section ParametricPrimitive

variable {X F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Variable upper limits, with the topological parameter restricted to
an arbitrary set. There is no local compactness assumption. -/
theorem continuousOn_parametric_primitive_univ_topological
    {f : X × ℝ → F} {U : Set X}
    (hf : ContinuousOn f (U ×ˢ (univ : Set ℝ))) (a : ℝ) :
    ContinuousOn (fun p : X × ℝ => ∫ t in a..p.2, f (p.1, t))
      (U ×ˢ (univ : Set ℝ)) := by
  have hcomp : ContinuousOn
      (fun p : (X × ℝ) × ℝ => f (p.1.1, a + (p.1.2 - a) * p.2))
      ((U ×ˢ (univ : Set ℝ)) ×ˢ uIcc (0 : ℝ) 1) :=
    hf.comp
      (continuous_fst.fst.prodMk
        (continuous_const.add
          ((continuous_fst.snd.sub continuous_const).mul continuous_snd))).continuousOn
      (fun p hp => ⟨hp.1.1, mem_univ _⟩)
  have hi : ContinuousOn
      (fun p : X × ℝ => ∫ u in (0 : ℝ)..1, f (p.1, a + (p.2 - a) * u))
      (U ×ˢ (univ : Set ℝ)) :=
    continuousOn_parametric_intervalIntegral_topological hcomp
  have hs : ContinuousOn
      (fun p : X × ℝ => (p.2 - a) •
        ∫ u in (0 : ℝ)..1, f (p.1, a + (p.2 - a) * u))
      (U ×ˢ (univ : Set ℝ)) :=
    (continuous_snd.sub continuous_const).continuousOn.smul hi
  apply hs.congr
  intro p _
  symm
  simpa using intervalIntegral.smul_integral_comp_add_mul
    (fun t => f (p.1, t)) (a := (0 : ℝ)) (b := 1) (p.2 - a) a

end ParametricPrimitive

section MultilinearIntegral

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- A genuine continuous multilinear map obtained by pointwise integration.
The direction space is topological and need not admit a norm. -/
def topologicalMultilinearIntervalIntegral {n : ℕ}
    (A : ℝ → E [×n]→L[ℝ] ℝ)
    (hA : Continuous (fun p : (Fin n → E) × ℝ => A p.2 p.1)) (a b : ℝ) :
    E [×n]→L[ℝ] ℝ := by
  classical
  have hi (v : Fin n → E) : IntervalIntegrable (fun t => A t v) volume a b :=
    (hA.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  refine
    { toMultilinearMap := MultilinearMap.mk'
        (fun v => ∫ t in a..b, A t v) ?_ ?_
      cont := continuous_parametric_intervalIntegral_topological hA a b }
  · intro v i x y
    simp only [ContinuousMultilinearMap.map_update_add]
    exact intervalIntegral.integral_add (hi (Function.update v i x))
      (hi (Function.update v i y))
  · intro v i c x
    simp only [ContinuousMultilinearMap.map_update_smul]
    exact intervalIntegral.integral_smul c (fun t => A t (Function.update v i x))

@[simp] theorem topologicalMultilinearIntervalIntegral_apply {n : ℕ}
    (A : ℝ → E [×n]→L[ℝ] ℝ)
    (hA : Continuous (fun p : (Fin n → E) × ℝ => A p.2 p.1))
    (a b : ℝ) (v : Fin n → E) :
    topologicalMultilinearIntervalIntegral A hA a b v = ∫ t in a..b, A t v := rfl

end MultilinearIntegral

section Volterra

variable {X E : Type*} [TopologicalSpace X]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

def volterraPrimitive (K : X × ℝ → ℝ) (p : X × ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..p.2, K (p.1, r)

def volterraWeightedForcing {n : ℕ} (K : X × ℝ → ℝ)
    (A : X × ℝ → E [×n]→L[ℝ] ℝ) (p : X × ℝ) : E [×n]→L[ℝ] ℝ :=
  Real.exp (-volterraPrimitive K p) • A p

def volterraValue {n : ℕ} (K : X × ℝ → ℝ)
    (A : X × ℝ → E [×n]→L[ℝ] ℝ) (p : X × ℝ) (v : Fin n → E) : ℝ :=
  Real.exp (volterraPrimitive K p) *
    ∫ t in (0 : ℝ)..p.2, volterraWeightedForcing K A (p.1, t) v

theorem continuousOn_volterraPrimitive {K : X × ℝ → ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ))) :
    ContinuousOn (volterraPrimitive K) (U ×ˢ (univ : Set ℝ)) :=
  continuousOn_parametric_primitive_univ_topological hK 0

theorem continuousOn_volterraWeightedForcing {n : ℕ} {K : X × ℝ → ℝ}
    {A : X × ℝ → E [×n]→L[ℝ] ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ)))
    (hA : ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)) :
    ContinuousOn (fun p : (X × ℝ) × (Fin n → E) =>
      volterraWeightedForcing K A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) := by
  have hi := (continuousOn_volterraPrimitive hK).comp
    continuous_fst.continuousOn (fun p hp => hp.1)
  have he := Real.continuous_exp.comp_continuousOn hi.neg
  simpa only [volterraWeightedForcing, smul_apply, smul_eq_mul] using he.mul hA

theorem continuousOn_volterraValue {n : ℕ} {K : X × ℝ → ℝ}
    {A : X × ℝ → E [×n]→L[ℝ] ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ)))
    (hA : ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)) :
    ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => volterraValue K A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) := by
  have hw := continuousOn_volterraWeightedForcing hK hA
  have hg : ContinuousOn
      (fun p : (X × (Fin n → E)) × ℝ =>
        volterraWeightedForcing K A (p.1.1, p.2) p.1.2)
      ((U ×ˢ (univ : Set (Fin n → E))) ×ˢ (univ : Set ℝ)) :=
    hw.comp
      ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd).continuousOn
      (fun p hp => ⟨⟨hp.1.1, mem_univ _⟩, mem_univ _⟩)
  have hprimitive := continuousOn_parametric_primitive_univ_topological hg 0
  have hinner : ContinuousOn
      (fun p : (X × ℝ) × (Fin n → E) =>
        ∫ t in (0 : ℝ)..p.1.2, volterraWeightedForcing K A (p.1.1, t) p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) :=
    hprimitive.comp
      ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd).continuousOn
      (fun p hp => ⟨⟨hp.1.1, mem_univ _⟩, mem_univ _⟩)
  have houter := (continuousOn_volterraPrimitive hK).comp
    continuous_fst.continuousOn (fun p hp => hp.1)
  exact (Real.continuous_exp.comp_continuousOn houter).mul hinner

private theorem continuous_volterraWeightedForcing_slice
    {n : ℕ} {K : X × ℝ → ℝ} {A : X × ℝ → E [×n]→L[ℝ] ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ)))
    (hA : ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)) {x : X} (hx : x ∈ U) :
    Continuous (fun p : (Fin n → E) × ℝ => volterraWeightedForcing K A (x, p.2) p.1) :=
  (continuousOn_volterraWeightedForcing hK hA).comp_continuous
    ((continuous_const.prodMk continuous_snd).prodMk continuous_fst)
    (fun p => ⟨⟨hx, mem_univ _⟩, mem_univ _⟩)

/-- The Volterra solution as an actual continuous multilinear map.
Outside the parameter domain its value is set to zero; every property is
proved on the original domain. -/
def volterraMultilinearMap {n : ℕ} {K : X × ℝ → ℝ}
    {A : X × ℝ → E [×n]→L[ℝ] ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ)))
    (hA : ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)) (p : X × ℝ) : E [×n]→L[ℝ] ℝ := by
  classical
  exact if hx : p.1 ∈ U then
    Real.exp (volterraPrimitive K p) • topologicalMultilinearIntervalIntegral
      (fun t => volterraWeightedForcing K A (p.1, t))
      (continuous_volterraWeightedForcing_slice hK hA hx) 0 p.2
  else 0

theorem volterraMultilinearMap_apply {n : ℕ} {K : X × ℝ → ℝ}
    {A : X × ℝ → E [×n]→L[ℝ] ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ)))
    (hA : ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)) {p : X × ℝ} (hp : p.1 ∈ U)
    (v : Fin n → E) : volterraMultilinearMap hK hA p v = volterraValue K A p v := by
  simp only [volterraMultilinearMap, dif_pos hp, smul_apply,
    topologicalMultilinearIntervalIntegral_apply, smul_eq_mul, volterraValue]

theorem continuousOn_volterraMultilinearMap {n : ℕ} {K : X × ℝ → ℝ}
    {A : X × ℝ → E [×n]→L[ℝ] ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ)))
    (hA : ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)) :
    ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => volterraMultilinearMap hK hA p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ) :=
  (continuousOn_volterraValue hK hA).congr
    (fun p hp => volterraMultilinearMap_apply hK hA hp.1.1 p.2)

theorem volterraMultilinearMap_zero {n : ℕ} {K : X × ℝ → ℝ}
    {A : X × ℝ → E [×n]→L[ℝ] ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ)))
    (hA : ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)) {x : X} (hx : x ∈ U) :
    volterraMultilinearMap hK hA (x, 0) = 0 := by
  ext v
  rw [volterraMultilinearMap_apply hK hA hx]
  simp only [volterraValue, intervalIntegral.integral_same, mul_zero, zero_apply]

theorem hasDerivAt_volterraValue_time {n : ℕ} {K : X × ℝ → ℝ}
    {A : X × ℝ → E [×n]→L[ℝ] ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ)))
    (hA : ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)) {x : X} (hx : x ∈ U)
    (v : Fin n → E) (t : ℝ) :
    HasDerivAt (fun r => volterraValue K A (x, r) v)
      (K (x, t) * volterraValue K A (x, t) v + A (x, t) v) t := by
  have hκ : Continuous (fun r : ℝ => K (x, r)) :=
    hK.comp_continuous (continuous_const.prodMk continuous_id)
      (fun r => ⟨hx, mem_univ _⟩)
  have hw : Continuous (fun r : ℝ => volterraWeightedForcing K A (x, r) v) :=
    (continuous_volterraWeightedForcing_slice hK hA hx).comp
      (continuous_const.prodMk continuous_id)
  have hI : HasDerivAt (fun r : ℝ => volterraPrimitive K (x, r)) (K (x, t)) t :=
    (hκ.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hd := hI.exp.mul (hw.integral_hasStrictDerivAt 0 t).hasDerivAt
  apply hd.congr_deriv
  have he : Real.exp (volterraPrimitive K (x, t)) *
      Real.exp (-volterraPrimitive K (x, t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simp only [volterraValue, volterraWeightedForcing, smul_apply, smul_eq_mul]
  calc
    _ = K (x, t) * (Real.exp (volterraPrimitive K (x, t)) *
          ∫ r in (0 : ℝ)..t,
            Real.exp (-volterraPrimitive K (x, r)) * A (x, r) v) +
        (Real.exp (volterraPrimitive K (x, t)) *
          Real.exp (-volterraPrimitive K (x, t))) * A (x, t) v := by ring
    _ = _ := by rw [he, one_mul]

theorem hasDerivAt_volterraMultilinearMap_time {n : ℕ} {K : X × ℝ → ℝ}
    {A : X × ℝ → E [×n]→L[ℝ] ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ)))
    (hA : ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)) {x : X} (hx : x ∈ U)
    (v : Fin n → E) (t : ℝ) :
    HasDerivAt (fun r => volterraMultilinearMap hK hA (x, r) v)
      (K (x, t) * volterraMultilinearMap hK hA (x, t) v + A (x, t) v) t := by
  have he : (fun r => volterraMultilinearMap hK hA (x, r) v) =
      fun r => volterraValue K A (x, r) v :=
    funext (fun r => volterraMultilinearMap_apply hK hA hx v)
  rw [he, volterraMultilinearMap_apply hK hA hx]
  exact hasDerivAt_volterraValue_time hK hA hx v t

/-- Uniqueness is proved from the true scalar time equation, not supplied
as a property of the constructed multilinear maps. -/
theorem eq_volterraMultilinearMap_of_timeODE {n : ℕ} {K : X × ℝ → ℝ}
    {A : X × ℝ → E [×n]→L[ℝ] ℝ} {U : Set X}
    (hK : ContinuousOn K (U ×ˢ (univ : Set ℝ)))
    (hA : ContinuousOn (fun p : (X × ℝ) × (Fin n → E) => A p.1 p.2)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ univ)) {x : X} (hx : x ∈ U)
    (v : Fin n → E) {y : ℝ → ℝ} (hy0 : y 0 = 0)
    (hy : ∀ t, HasDerivAt y (K (x, t) * y t + A (x, t) v) t) (t : ℝ) :
    y t = volterraMultilinearMap hK hA (x, t) v := by
  have hκ : Continuous (fun r : ℝ => K (x, r)) :=
    hK.comp_continuous (continuous_const.prodMk continuous_id)
      (fun r => ⟨hx, mem_univ _⟩)
  have hforcing : Continuous (fun r : ℝ => A (x, r) v) :=
    hA.comp_continuous ((continuous_const.prodMk continuous_id).prodMk continuous_const)
      (fun r => ⟨⟨hx, mem_univ _⟩, mem_univ _⟩)
  have he := scalar_inhomogeneousODE_eq_exp_mul_global hκ hforcing hy 0 t
  rw [volterraMultilinearMap_apply hK hA hx]
  simpa only [hy0, zero_add, volterraValue, volterraPrimitive,
    volterraWeightedForcing, smul_apply, smul_eq_mul] using he

end Volterra

end ContinuousFlexibility.Analysis
