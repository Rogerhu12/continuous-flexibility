module

public import ContinuousFlexibility.Radial.BufferIntervalDomain
public import ContinuousFlexibility.Radial.PositiveBufferTraceMap

/-!
# Compact smooth tests determine the actual energy form

The supplied closed-form realization states density in the public graph
product. The coordinate homeomorphism transfers that exact density to the
Hilbert energy space. Consequently a compact-test Green identity extends to
every actual energy field, including point evaluation at the cut.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

/-- The Hilbert graph product and the public finite product have the same
topology, with exactly the same three coordinates. -/
def bufferEnergyTripleHomeomorph :
    PositiveBufferEnergyTriple ≃ₜ (RadialL2 × RadialL2 × RadialL2) where
  toFun := bufferEnergyTripleMap
  invFun := fun p => WithLp.toLp 2 ![p.1, p.2.1, p.2.2]
  left_inv := by
    intro z
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [bufferEnergyTripleMap_apply, PiLp.toLp_apply]
  right_inv := by
    intro p
    simp [bufferEnergyTripleMap_apply, PiLp.toLp_apply]
  continuous_toFun := bufferEnergyTripleMap.continuous
  continuous_invFun := by
    have h : Continuous (fun p : RadialL2 × RadialL2 × RadialL2 =>
        (![p.1, p.2.1, p.2.2] : Fin 3 → RadialL2)) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_fst
      · exact continuous_fst.comp continuous_snd
      · exact continuous_snd.comp continuous_snd
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => RadialL2)).comp h

@[simp] theorem bufferEnergyTripleHomeomorph_apply (z : PositiveBufferEnergyTriple) :
    bufferEnergyTripleHomeomorph z = (z 0, z 1, z 2) := bufferEnergyTripleMap_apply z

/-- The actual compact smooth lifts, retaining their derivative and weight. -/
def positiveBufferCompactLiftSet (V : ℝ → ℝ) (hV : Continuous V) :
    Set (PositiveBufferEnergy V) :=
  {u | ∃ φ : ℝ → ℝ, ∃ hφ : ContDiff ℝ ∞ φ, ∃ hc : HasCompactSupport φ,
    u = positiveBufferCompactEnergyLift V hV φ hφ hc}

theorem positiveBufferCompactLiftSet_image (V : ℝ → ℝ) (hV : Continuous V) :
    (fun u : PositiveBufferEnergy V => bufferEnergyTripleMap u.val) ''
      positiveBufferCompactLiftSet V hV = SchrodingerEnergyCore V := by
  ext p
  constructor
  · rintro ⟨u, ⟨φ, hφ, hc, rfl⟩, rfl⟩
    refine ⟨φ, hφ, hc, positiveBufferCompactEnergyLift_base_ae V hV φ hφ hc,
      positiveBufferCompactEnergyLift_derivative_ae V hV φ hφ hc, ?_⟩
    exact MemLp.coeFn_toLp (positiveBufferCompact_weight_memLp hV hφ hc)
  · rintro ⟨φ, hφ, hc, hp0, hp1, hp2⟩
    let v := positiveBufferCompactEnergyLift V hV φ hφ hc
    refine ⟨v, ⟨φ, hφ, hc, rfl⟩, ?_⟩
    change (v.val 0, v.val 1, v.val 2) = p
    apply Prod.ext
    · apply Lp.ext
      exact (positiveBufferCompactEnergyLift_base_ae V hV φ hφ hc).trans hp0.symm
    · apply Prod.ext
      · apply Lp.ext
        exact (positiveBufferCompactEnergyLift_derivative_ae V hV φ hφ hc).trans hp1.symm
      · apply Lp.ext
        exact (MemLp.coeFn_toLp (positiveBufferCompact_weight_memLp hV hφ hc)).trans hp2.symm

/-- The frozen public core-density assumption gives genuine density of
compact smooth lifts in the actual Hilbert energy space. -/
theorem positiveBufferCompactLiftSet_dense {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V) :
    Dense (positiveBufferCompactLiftSet V hV) := by
  let F : PositiveBufferEnergy V → RadialL2 × RadialL2 × RadialL2 :=
    fun u => bufferEnergyTripleMap u.val
  have hF : Topology.IsEmbedding F :=
    bufferEnergyTripleHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  intro u
  rw [hF.closure_eq_preimage_closure_image]
  change F u ∈ closure (F '' positiveBufferCompactLiftSet V hV)
  rw [positiveBufferCompactLiftSet_image, hreal.2.2.1]
  exact u.property

/-- A continuous functional on the actual energy space is determined by
its values on compact smooth lifts. -/
theorem positiveBufferEnergy_continuous_ext_compact {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V)
    {F G : PositiveBufferEnergy V → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ φ : ℝ → ℝ, ∀ hφ : ContDiff ℝ ∞ φ, ∀ hc : HasCompactSupport φ,
      F (positiveBufferCompactEnergyLift V hV φ hφ hc) =
        G (positiveBufferCompactEnergyLift V hV φ hφ hc)) : F = G := by
  funext u
  have hsubset : positiveBufferCompactLiftSet V hV ⊆ {v | F v = G v} := by
    rintro v ⟨φ, hφ, hc, rfl⟩
    exact hFG φ hφ hc
  exact closure_minimal hsubset (isClosed_eq hF hG)
    (positiveBufferCompactLiftSet_dense hreal hV u)

/-- The compact-test delta identity extends to every actual energy test.
The boundary coefficient multiplies the genuine continuous trace map. -/
theorem positiveBuffer_delta_energy_of_compact {V : ℝ → ℝ}
    (hreal : ActualClosedFormRealization V) (hV : Continuous V)
    (e : PositiveBufferEnergy V) (f : RadialL2) (c jump : ℝ)
    (hcompact : ∀ φ : ℝ → ℝ, ∀ hφ : ContDiff ℝ ∞ φ, ∀ hc : HasCompactSupport φ,
      positiveBufferEnergyForm V hV e (positiveBufferCompactEnergyLift V hV φ hφ hc) =
        inner (𝕜 := ℝ) f
          (positiveBufferEnergyCoordinate V 0 (positiveBufferCompactEnergyLift V hV φ hφ hc)) +
        jump * φ c)
    (v : PositiveBufferEnergy V) :
    positiveBufferEnergyForm V hV e v =
      inner (𝕜 := ℝ) f (positiveBufferEnergyCoordinate V 0 v) +
        jump * positiveBufferTraceAt V c v := by
  have hinner : Continuous (fun v : PositiveBufferEnergy V =>
      inner (𝕜 := ℝ) f (positiveBufferEnergyCoordinate V 0 v)) :=
    (innerSL ℝ f).continuous.comp (positiveBufferEnergyCoordinate V 0).continuous
  have hright : Continuous (fun v : PositiveBufferEnergy V =>
      inner (𝕜 := ℝ) f (positiveBufferEnergyCoordinate V 0 v) +
        jump * positiveBufferTraceAt V c v) :=
    hinner.add (continuous_const.mul (positiveBufferTraceAt V c).continuous)
  have heq := positiveBufferEnergy_continuous_ext_compact hreal hV
    (positiveBufferEnergyForm V hV e).continuous
    hright
    (fun φ hφ hc => by
      rw [positiveBufferTraceAt_eq V c _ hφ.continuous
        (positiveBufferCompactEnergyLift_base_ae V hV φ hφ hc)]
      exact hcompact φ hφ hc)
  exact congrFun heq v

end ContinuousFlexibility.Radial
