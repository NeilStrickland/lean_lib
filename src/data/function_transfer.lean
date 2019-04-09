import data.equiv.basic

open equiv

universes u v w x

def function_equiv_of_equiv {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
 (f : α ≃ γ) (g : β ≃ δ) : (α → β) ≃ (γ → δ) := 
{
  to_fun := λ (u : α → β), g ∘ u ∘ f.inv_fun,
  inv_fun := λ (v : γ → δ), g.inv_fun ∘ v ∘ f,
  left_inv := begin
   unfold function.left_inverse,
   intro u, ext a, simp,
   by calc
    g.inv_fun (g.to_fun (u (f.inv_fun (f.to_fun a)))) = 
     u (f.inv_fun (f.to_fun a)) : g.left_inv _
    ... = u a : congr_arg u (f.left_inv a),
  end,
  right_inv := begin
    unfold function.right_inverse,
    intro v, ext c, simp, 
   by calc
    g.to_fun (g.inv_fun (v (f.to_fun (f.inv_fun c)))) = v (f.to_fun (f.inv_fun c)) : g.right_inv _
     ... = v c : congr_arg v (f.right_inv c)
  end  
}



