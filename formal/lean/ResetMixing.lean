import IncrementCycles

open scoped BigOperators Topology
open Filter
namespace IncrementCycles.ResetMixing
noncomputable section

variable {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H]

def uniform (H : Type*) [Fintype H] : ℝ := ((Fintype.card H : ℝ))⁻¹

def kernel (c : Equiv.Perm H) (ρ : ℝ) (i j : H) : ℝ :=
  (if c i = j then 1-ρ else 0) + ρ * uniform H

def power (K : H → H → ℝ) : ℕ → H → H → ℝ
  | 0, i, j => if i=j then 1 else 0
  | n+1, i, j => ∑ k, power K n i k * K k j

omit [DecidableEq H] in
theorem uniform_mass : ∑ _ : H, uniform H = 1 := by
  simp [uniform, Fintype.card_ne_zero]

theorem row_sum (c : Equiv.Perm H) (ρ : ℝ) (i : H) :
    ∑ j, kernel c ρ i j = 1 := by
  simp only [kernel, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [uniform, Fintype.card_ne_zero]

theorem col_sum (c : Equiv.Perm H) (ρ : ℝ) (j : H) :
    ∑ i, kernel c ρ i j = 1 := by
  simp only [kernel, Finset.sum_add_distrib, ← Finset.mul_sum, c.apply_eq_iff_eq_symm_apply]
  simp [uniform, Fintype.card_ne_zero]

theorem stationary (c : Equiv.Perm H) (ρ : ℝ) (j : H) :
    ∑ i, uniform H * kernel c ρ i j = uniform H := by
  rw [← Finset.mul_sum,col_sum,mul_one]

omit [Nonempty H] in
theorem kernel_nonnegative (c : Equiv.Perm H) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (i j : H) :
    0 ≤ kernel c ρ i j := by
  unfold kernel uniform
  split <;> positivity

/-- Exact transition probability after n steps. The second term counts trajectories
with at least one reset. -/
theorem power_formula (c : Equiv.Perm H) (ρ : ℝ) (n : ℕ) (i j : H) :
    power (kernel c ρ) n i j =
      (if c^[n] i = j then (1-ρ)^n else 0) + (1-(1-ρ)^n)*uniform H := by
  induction n generalizing i j with
  | zero => simp [power]
  | succ n ih =>
    simp only [power, ih, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
      ← Finset.mul_sum, col_sum, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Function.iterate_succ_apply', pow_succ]
    unfold kernel
    split <;> ring

theorem mixing (c : Equiv.Perm H) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) (i j : H) :
    Tendsto (fun n => power (kernel c ρ) n i j) atTop (𝓝 (uniform H)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr h1)
    (show 1-ρ < 1 by linarith)
  have hw : Tendsto (fun n : ℕ => if c^[n] i=j then (1-ρ)^n else 0) atTop (𝓝 0) := by
    apply squeeze_zero _ _ hp
    · intro n
      split <;> positivity
    · intro n
      split
      · exact le_rfl
      · exact pow_nonneg (sub_nonneg.mpr h1) _
  simpa only [power_formula, zero_add, sub_zero, one_mul] using
    hw.add ((tendsto_const_nhds (x := (1:ℝ))).sub hp |>.mul_const (uniform H))

def sixCycle : Equiv.Perm (Fin 6) := Equiv.addRight 1
def twelveCycles : Equiv.Perm (Bool × Fin 6) := Equiv.prodCongr (Equiv.refl Bool) sixCycle

theorem control_kernel (ρ : ℝ) (i j : Bool × Fin 6) :
    kernel twelveCycles ρ i j = controlKernel ρ i j := by
  have h : twelveCycles i = ctrlAdvance i := rfl
  simp [kernel,h,controlKernel,uniform,div_eq_mul_inv]

end
end IncrementCycles.ResetMixing
