import ResetMixing

open scoped BigOperators
open IncrementCycles ResetMixing
namespace CycleExpansion
noncomputable section

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Two consecutive emissions, summed over the stationary hidden pair. -/
def emittedPairs (mass : ℝ) (K : H → H → ℝ) (h : H → S) (f g : Readout) :=
  mass*(∑ i, ∑ j, f (h i)*K i j*g (h j))

theorem reset_pair_split (c : Equiv.Perm H) (ρ : ℝ) (h : H → S) (f g : Readout) :
    emittedPairs (uniform H) (kernel c ρ) h f g =
    (1-ρ)*(uniform H * ∑ i, f (h i)*g (h (c i))) +
      ρ*(uniform H * ∑ i, f (h i))*(uniform H * ∑ j, g (h j)) := by
  have hs (i : H) :
      (∑ j, f (h i)*kernel c ρ i j*g (h j)) =
      (1-ρ)*(f (h i)*g (h (c i))) + (ρ*uniform H*(∑ j, g (h j)))*f (h i) := by
    simp only [kernel,mul_add,add_mul,mul_ite,mul_zero,ite_mul,zero_mul,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum]
    ring
  simp only [emittedPairs,hs,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

theorem six_pair (ρ : ℝ) (f g : Readout) :
    emittedPairs (1/6) (kernel sixCycle ρ) cycleSymbol f g = directed2 ρ f g := by
  have hu : uniform (Fin 6) = 1/6 := by norm_num [uniform]
  rw [← hu,reset_pair_split,hu]
  norm_num [sixCycle,Equiv.addRight,cycleSymbol,Fin.sum_univ_succ,directed2,cyc2,mean,
    Fin.val_add,Fin.val_ofNat]
  ring

theorem twelve_pair (ρ : ℝ) (f g : Readout) :
    emittedPairs (1/12) (controlKernel ρ) ctrlEmission f g = ctrl2 ρ f g := by
  have hu : uniform (Bool × Fin 6) = 1/12 := by norm_num [uniform]
  have hk : controlKernel ρ = kernel twelveCycles ρ :=
    funext (fun i => funext (fun j => (control_kernel ρ i j).symm))
  rw [hk,← hu,reset_pair_split,hu]
  simp only [Fintype.sum_prod_type]
  norm_num [Fintype.sum_bool,Fin.sum_univ_succ,twelveCycles,sixCycle,Equiv.addRight,
    ctrlEmission,cycleSymbol,ctrl2,directed2,cyc2,mean,IncrementCycles.flip,
    Fin.val_neg',Fin.val_add,Fin.val_ofNat]
  ring

theorem observed_pairs_match (ρ η : ℝ) (a b : S) :
    emittedPairs (1/6) (kernel sixCycle ρ) cycleSymbol (em η · a) (em η · b) =
    emittedPairs (1/12) (controlKernel ρ) ctrlEmission (em η · a) (em η · b) := by
  rw [six_pair,twelve_pair,same_adjacent]

def avg (x : H → ℝ) := uniform H * ∑ i, x i

/-- The two transition-emission sums conditional on the central hidden state. -/
def emittedThree (mass : ℝ) (K : H → H → ℝ) (f g h : H → ℝ) :=
  mass * ∑ j, (∑ i, f i*K i j)*g j*(∑ k, K j k*h k)

theorem reset_three_split (c : Equiv.Perm H) (ρ : ℝ) (f g h : H → ℝ) :
    emittedThree (uniform H) (kernel c ρ) f g h =
    (1-ρ)^2*avg (fun j => f (c.symm j)*g j*h (c j)) +
    ρ*(1-ρ)*(avg f*avg (fun j => g j*h (c j)) + avg (fun j => f (c.symm j)*g j)*avg h) +
    ρ^2*avg f*avg g*avg h := by
  have hs (j : H) : (∑ i, f i * kernel c ρ i j) = (1-ρ)*f (c.symm j) + ρ*avg f := by
    simp only [kernel,mul_add,mul_ite,mul_zero, c.apply_eq_iff_eq_symm_apply,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul,avg]
    ring
  have ht (j : H) : (∑ k, kernel c ρ j k * h k) = (1-ρ)*h (c j) + ρ*avg h := by
    simp only [kernel,add_mul,ite_mul,zero_mul,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum,avg]
    ring
  have expand (j : H) : ((1-ρ)*f (c.symm j)+ρ*avg f)*g j*((1-ρ)*h (c j)+ρ*avg h) =
      (1-ρ)^2*(f (c.symm j)*g j*h (c j)) +
      (ρ*(1-ρ)*avg f)*(g j*h (c j)) + (ρ*(1-ρ)*avg h)*(f (c.symm j)*g j) +
      (ρ^2*avg f*avg h)*g j := by ring
  simp only [emittedThree,hs,ht]
  simp only [expand,Finset.sum_add_distrib,← Finset.mul_sum]
  unfold avg
  ring

theorem reset_lag_two_split [Nonempty H] (c : Equiv.Perm H) (ρ : ℝ) (f h : H → ℝ) :
    emittedThree (uniform H) (kernel c ρ) f (fun _ => 1) h =
    (1-ρ)^2*avg (fun j => f (c.symm j)*h (c j)) +
    (1-(1-ρ)^2)*avg f*avg h := by
  have hx : avg (fun j => f (c.symm j)) = avg f := by unfold avg; rw [Equiv.sum_comp]
  have hy : avg (fun j => h (c j)) = avg h := by unfold avg; rw [Equiv.sum_comp]
  have ho : avg (fun _ : H => (1:ℝ)) = 1 := by simp [avg,uniform,Fintype.card_ne_zero]
  rw [reset_three_split]
  simp only [mul_one,one_mul,hx,hy,ho]
  ring

theorem six_three (ρ : ℝ) (f g h : Readout) :
    emittedThree (1/6) (kernel sixCycle ρ) (f ∘ cycleSymbol) (g ∘ cycleSymbol) (h ∘ cycleSymbol) =
      directed3 ρ f g h := by
  have hu : uniform (Fin 6) = 1/6 := by norm_num [uniform]
  rw [← hu,reset_three_split]
  norm_num [avg,hu,sixCycle,Equiv.addRight,cycleSymbol,Fin.sum_univ_succ,directed3,
    cyc3,cyc2,mean,Fin.val_add,Fin.val_sub,Fin.val_neg',Fin.val_ofNat,Function.comp_def]
  ring

theorem six_lag_two (ρ : ℝ) (f h : Readout) :
    emittedThree (1/6) (kernel sixCycle ρ) (f ∘ cycleSymbol) (fun _ => 1) (h ∘ cycleSymbol) =
      lag2 ρ f h := by
  have hu : uniform (Fin 6) = 1/6 := by norm_num [uniform]
  rw [← hu,reset_lag_two_split]
  norm_num [avg,hu,sixCycle,Equiv.addRight,cycleSymbol,Fin.sum_univ_succ,lag2,
    cyc2,mean,Fin.val_add,Fin.val_sub,Fin.val_neg',Fin.val_ofNat,Function.comp_def]
  ring

theorem twelve_three (ρ : ℝ) (f g h : Readout) :
    emittedThree (1/12) (controlKernel ρ) (f ∘ ctrlEmission) (g ∘ ctrlEmission) (h ∘ ctrlEmission) =
      ctrl3 ρ f g h := by
  have hu : uniform (Bool × Fin 6) = 1/12 := by norm_num [uniform]
  have hk : controlKernel ρ = kernel twelveCycles ρ :=
    funext (fun i => funext (fun j => (control_kernel ρ i j).symm))
  rw [hk,← hu,reset_three_split]
  norm_num [avg,hu,Fintype.sum_prod_type,Fintype.sum_bool,twelveCycles,ctrlEmission,
    ctrl3,ctrlLag2,ctrl2,directed2,IncrementCycles.flip,sixCycle,Equiv.addRight,cycleSymbol,Fin.sum_univ_succ,directed3,
    cyc3,cyc2,mean,Fin.val_add,Fin.val_sub,Fin.val_neg',Fin.val_ofNat,Function.comp_def]
  ring

theorem twelve_lag_two (ρ : ℝ) (f h : Readout) :
    emittedThree (1/12) (controlKernel ρ) (f ∘ ctrlEmission) (fun _ => 1) (h ∘ ctrlEmission) =
      ctrlLag2 ρ f h := by
  have hu : uniform (Bool × Fin 6) = 1/12 := by norm_num [uniform]
  have hk : controlKernel ρ = kernel twelveCycles ρ :=
    funext (fun i => funext (fun j => (control_kernel ρ i j).symm))
  rw [hk,← hu,reset_lag_two_split]
  norm_num [avg,hu,Fintype.sum_prod_type,Fintype.sum_bool,twelveCycles,ctrlEmission,
    ctrl3,ctrlLag2,ctrl2,directed2,IncrementCycles.flip,sixCycle,Equiv.addRight,cycleSymbol,Fin.sum_univ_succ,lag2,
    cyc2,mean,Fin.val_add,Fin.val_sub,Fin.val_neg',Fin.val_ofNat,Function.comp_def]
  ring

end
end CycleExpansion
